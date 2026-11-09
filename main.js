const { Plugin, ItemView, PluginSettingTab, Setting, Notice, Modal, TFile, TFolder, normalizePath, setIcon } = require('obsidian');
const VIEW = 'candoln-visual-planner-view';
const DEFAULTS = { databasePath: '', folder: '', statusField: 'plan-status', doneValue: '已完成', activeValue: '進行中', dateField: 'plan-date', kindField: 'plan-type', completedAtField: 'plan-completed-at', noteFilter: 'all', pageField: '', orderField: 'vp-order', pageOrder: [], compactMode: false, verticalGap: 12, horizontalGap: 42 };
const TYPES = ['方向','目標','計畫','任務','研究'];
const todayLocal = () => { const d = new Date(); return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`; };
const stampLocal = () => { const d=new Date(); return `${todayLocal()}T${String(d.getHours()).padStart(2,'0')}:${String(d.getMinutes()).padStart(2,'0')}`; };
const uid = () => `lmd-item-${(typeof crypto!=='undefined' && crypto.randomUUID ? crypto.randomUUID() : `${Date.now()}-${Math.random().toString(36).slice(2)}`)}`;
const getFm = (app,f) => app.metadataCache.getFileCache(f)?.frontmatter || {};
const prop = (fm,key) => fm?.[key] ?? '';
const text = x => x == null ? '' : String(x).trim();
const folderOf = p => p.includes('/') ? p.slice(0,p.lastIndexOf('/')) : '';
const sanitizeName = n => text(n).replace(/[\\/:*?"<>|]/g,'-').replace(/\.+$/g,'').trim().slice(0,120) || '未命名';
const isDescendant = (id,ancestor,byId) => { const seen=new Set(); let at=id; while(at && !seen.has(at)) { if(at===ancestor)return true; seen.add(at); at=byId.get(at)?.parent || ''; } return false; };
const el=(parent,tag,cls,txt)=> { const out=parent.createEl(tag,{cls}); if(txt!==undefined) out.setText(String(txt)); return out; };
const btn=(parent,label,callback,cls='')=>{const b=el(parent,'button',`vp-btn ${cls}`,label); b.addEventListener('click',callback);return b;};
function buildModel(nodes){
  const ids=new Map(), duplicates=new Set();
  for(const n of nodes){if(ids.has(n.id))duplicates.add(n.id);else ids.set(n.id,n);}
  const byId=new Map([...ids].filter(([id])=>!duplicates.has(id)));
  const warnings=[]; for(const id of duplicates)warnings.push(`重複 ID：${id}（已停用這些項目的父子寫入）`);
  const children=new Map(),roots=[];
  for(const n of nodes){
    if(duplicates.has(n.id)){roots.push({...n,issue:'重複 ID'});continue;}
    if(n.parent && !byId.has(n.parent)){warnings.push(`找不到父項：${n.file.path} → ${n.parent}`); roots.push({...n,issue:'找不到父項'});continue;}
    if(n.parent && isDescendant(n.parent,n.id,byId)){warnings.push(`循環父子關係：${n.file.path}`);roots.push({...n,issue:'循環關係'});continue;}
    if(n.parent){if(!children.has(n.parent))children.set(n.parent,[]);children.get(n.parent).push(n);} else roots.push(n);
  }
  const sort=(xs)=>xs.sort((a,b)=>(Number.isFinite(a.order)?a.order:1e12)-(Number.isFinite(b.order)?b.order:1e12)||a.file.basename.localeCompare(b.file.basename,'zh-Hant'));
  sort(roots);for(const cs of children.values())sort(cs);
  return {byId,duplicates,children,roots,warnings};
}
// Order changes are calculated against the complete, unfiltered tree.
// Dragging a parent moves the entire subtree; descendant selections are not
// flattened into the destination. This helper does not mutate its inputs.
function planReorder(model, selectedIds, targetId, placement){
  if(!['before','after','inside'].includes(placement))throw new Error('無效的拖放位置');
  const target=model.byId.get(targetId);
  if(!target || model.duplicates.has(targetId))throw new Error('找不到有效的目標節點');
  const selected=[...new Set(selectedIds)];
  if(!selected.length || selected.some(id=>!model.byId.has(id)||model.duplicates.has(id)))throw new Error('選取包含無效或重複 ID');
  const selectedSet=new Set(selected);
  // Drop targets cannot be selected nodes or their descendants.
  if(selectedSet.has(targetId))throw new Error('不能把節點放到選取集合本身');
  const moving=selected.map(id=>model.byId.get(id)).filter(node=>{
    let p=node.parent;const seen=new Set();
    while(p&&!seen.has(p)){if(selectedSet.has(p))return false;seen.add(p);p=model.byId.get(p)?.parent||'';}
    return true;
  });
  const destinationParent=placement==='inside'?targetId:(target.parent||'');
  for(const node of moving){
    if(destinationParent && (destinationParent===node.id||isDescendant(destinationParent,node.id,model.byId)))throw new Error('不能把節點移到自己的後代');
  }
  // Preserve existing visible order, not Ctrl-click selection order.
  const positions=new Map();let orderIndex=0;
  const visit=node=>{if(positions.has(node.id))return;positions.set(node.id,orderIndex++);for(const child of model.children.get(node.id)||[])visit(child);};
  for(const root of model.roots)visit(root);
  moving.sort((a,b)=>(positions.get(a.id)??1e9)-(positions.get(b.id)??1e9));
  const movingSet=new Set(moving.map(n=>n.id));
  const siblingsOf=parent=>(parent?model.children.get(parent):model.roots)||[];
  const destination=siblingsOf(destinationParent).filter(n=>!movingSet.has(n.id));
  let at=destination.length;
  if(placement!=='inside'){
    const targetIndex=destination.findIndex(n=>n.id===targetId);
    if(targetIndex<0)throw new Error('目標不在預期的同層');
    at=targetIndex+(placement==='after'?1:0);
  }
  destination.splice(at,0,...moving);
  const affectedParents=new Set(moving.map(n=>n.parent||''));
  affectedParents.add(destinationParent);
  const next=new Map();
  for(const parent of affectedParents){
    const siblings=parent===destinationParent?destination:siblingsOf(parent).filter(n=>!movingSet.has(n.id));
    siblings.forEach((node,index)=>{
      const newParent=movingSet.has(node.id)?destinationParent:(node.parent||'');
      const newOrder=(index+1)*100;
      if((node.parent||'')!==newParent || node.order!==newOrder)next.set(node.id,{node,parent:newParent,order:newOrder});
    });
  }
  return {updates:[...next.values()],moved:moving};
}

// Resolve drop intent from card geometry (screen pixels, independent of zoom).
// Inside a card = make it the parent. In the narrow surrounding gutter =
// insert BEFORE/AFTER it. This function intentionally never treats the top
// or bottom region *inside* a card as a reorder drop.
function findMapDropTarget(cards,x,y){
  const geometry=cards.map(other=>({other,rect:other.getBoundingClientRect()}));
  for(const item of geometry){
    const r=item.rect;
    if(x>=r.left&&x<=r.right&&y>=r.top&&y<=r.bottom)return {...item,placement:'inside'};
  }
  let best=null,score=Infinity;
  for(const item of geometry){
    const r=item.rect;
    // Side gutters remain usable even when the vertical spacing is set to 0.
    const beside=(x>=r.left-56&&x<r.left)||(x>r.right&&x<=r.right+56);
    const nearX=x>=r.left-24&&x<=r.right+24;
    for(const placement of ['before','after']){
      const edge=placement==='before'?r.top:r.bottom;
      const dy=Math.abs(y-edge);
      // Normal horizontal insertion gutter: within 24px of a card edge.
      // Beside the card: use upper/lower half for the sibling indicator.
      const allowed=(nearX&&dy<=24)||(beside&&y>=r.top-24&&y<=r.bottom+24);
      if(!allowed)continue;
      const distance=beside ? Math.abs(y-(placement==='before'?r.top:r.bottom))*.35 : dy;
      const dx=x<r.left?r.left-x:x>r.right?x-r.right:0;
      const candidateScore=distance+dx*.18;
      if(candidateScore<score){score=candidateScore;best={...item,placement};}
    }
  }
  return best;
}

class TextPrompt extends Modal {
 constructor(app,{title,label,value='',confirm='確認',onSubmit}){super(app);Object.assign(this,{title,label,value,confirm,onSubmit});}
 onOpen(){this.contentEl.empty();this.titleEl.setText(this.title);const form=this.contentEl.createEl('form');const p=form.createEl('label');p.setText(this.label);const input=form.createEl('input',{type:'text'});input.style.width='100%';input.value=this.value;const actions=form.createDiv({cls:'vp-modal-actions'});const cancel=actions.createEl('button',{text:'取消',type:'button'});cancel.onclick=()=>this.close();const ok=actions.createEl('button',{text:this.confirm,type:'submit',cls:'mod-cta'});form.onsubmit=e=>{e.preventDefault();const v=input.value.trim();if(!v)return;this.close();void this.onSubmit(v);};setTimeout(()=>input.focus(),0);}
 onClose(){this.contentEl.empty();}
}
class DatePrompt extends Modal {
 constructor(app,{title,value,onSubmit}){super(app);Object.assign(this,{title,value,onSubmit});}
 onOpen(){this.contentEl.empty();this.titleEl.setText(this.title);const form=this.contentEl.createEl('form');
   form.createEl('p',{text:this.title.startsWith('批量安排')?'設定選取節點的計畫日期，不會修改完成日期。':'完成日期可選過去的時間；計畫執行日期不會被修改。'});
   const field=form.createEl('input',{type:'datetime-local'});field.value=this.value.replace(' ','T').slice(0,16);field.style.width='100%';
   const actions=form.createDiv({cls:'vp-modal-actions'});const cancel=actions.createEl('button',{text:'取消',type:'button'});cancel.onclick=()=>this.close();
   actions.createEl('button',{text:this.title.startsWith('批量安排')?'套用日期':'確認完成',type:'submit',cls:'mod-cta'});
   form.onsubmit=e=>{e.preventDefault();if(!/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}$/.test(field.value)){new Notice('請選擇日期與時間');return;}const value=field.value;this.close();void this.onSubmit(value);};
 }
 onClose(){this.contentEl.empty();}
}
class PlannerView extends ItemView {
 constructor(leaf,plugin){super(leaf);this.plugin=plugin;this.nodes=[];this.model=buildModel([]);this.filter='';this.focus='';this.tab='map';this.collapsed=new Set();this.mapScale=1;this.mapPan={x:24,y:32};this.mapPanInitialized=false;this.selected='';this.page='__all__';this.pageCameras=new Map();this.detailsOpen=false;this.dbSchema=[];this.busy=false;this.calendarMonth=todayLocal().slice(0,7);this.calendarDateMode='planned';this.calendarPage='__all__';this._refreshSeq=0;this.multiSelected=new Set();this.selectionAnchor='';this.visibleOrder=[];this._pendingReorders=new Map();}
 getViewType(){return VIEW;}
 getDisplayText(){return '視覺規劃';}
 getIcon(){return 'git-fork';}
 async onOpen(){await this.refresh();}
 async onClose(){this._refreshSeq++;}
 async databaseSource(){
   const path=this.plugin.settings.databasePath;
   if(!path)return {folder:null,error:'尚未指定規劃專用 .database，請到插件設定選擇。'};
   const db=this.app.vault.getAbstractFileByPath(path);
   if(!(db instanceof TFile) || db.extension!=='database')return {folder:null,error:`找不到資料庫：${path}`};
   let def;try{def=JSON.parse(await this.app.vault.read(db));}catch(e){return {folder:null,error:`資料庫 JSON 解析失敗：${e.message}`};}
   if(def.source?.type!=='folder'||typeof def.source.path!=='string')return {folder:null,error:'目前只支援以單一資料夾作為來源的 .database（不支援 database-set）。'};
   const folder=def.source.path?this.app.vault.getAbstractFileByPath(normalizePath(def.source.path)):this.app.vault.getRoot();
   if(!(folder instanceof TFolder))return {folder:null,error:`找不到資料來源資料夾：${def.source.path}`};
   return {folder,error:'',database:db,schema:Array.isArray(def.schema)?def.schema:[]};
 }
 async refresh(){
   const seq=++this._refreshSeq;const source=await this.databaseSource();
   if(seq!==this._refreshSeq)return;
   this.source=source;this.dbSchema=source.schema||[];
   const files=source.folder?source.folder.children.filter(f=>f instanceof TFile && f.extension==='md'):[];
   const nodes=[];
   for(const file of files){const fm=getFm(this.app,file);const id=text(prop(fm,'lmd-id'));if(!id)continue;
     nodes.push({id,parent:text(prop(fm,'lmd-parent')),file,status:text(prop(fm,this.plugin.settings.statusField)),kind:text(prop(fm,this.plugin.settings.kindField))||'未分類',date:text(prop(fm,this.plugin.settings.dateField)),completedAt:text(prop(fm,this.plugin.settings.completedAtField)),page:text(prop(fm,this.plugin.settings.pageField)),order:(Number.isFinite(Number(prop(fm,this.plugin.settings.orderField)))&&text(prop(fm,this.plugin.settings.orderField))!==''?Number(prop(fm,this.plugin.settings.orderField)):null)});
   }
   if(seq!==this._refreshSeq)return;
   // The Obsidian metadata cache can lag behind processFrontMatter(). Keep the
   // committed on-disk order visible until the corresponding cache entry catches up.
   for(const n of nodes){
     const pending=this._pendingReorders.get(n.id);
     if(!pending)continue;
     if(n.parent===pending.parent&&n.order===pending.order)this._pendingReorders.delete(n.id);
     else{n.parent=pending.parent;n.order=pending.order;}
   }
   this.nodes=nodes;this.model=buildModel(nodes);this.multiSelected=new Set([...this.multiSelected].filter(id=>this.model.byId.has(id))); if(this.page!=='__all__'&&!this.getPageNames().includes(this.page))this.page='__all__';
   if(this.focus && !this.model.byId.has(this.focus))this.focus='';
   if(this.selected && !this.model.byId.has(this.selected))this.selected='';
   this.render();
 }
 select(id){this.selected=id;this.render();}
 isDone(n){return n.status===this.plugin.settings.doneValue;}
 async saveField(n,key,value){if(!n||this.model.duplicates.has(n.id)){new Notice('無法安全更新：ID 重複或項目不存在');return;}const f=this.app.vault.getAbstractFileByPath(n.file.path);if(!(f instanceof TFile))return;await this.app.fileManager.processFrontMatter(f,fm=>{if(value===null || value==='')delete fm[key];else fm[key]=value;});await this.refresh();}
 async setComplete(n,checked){
   if(this.busy)return;
   if(checked){
     const modal=new DatePrompt(this.app,{title:'標記完成',value:n.completedAt||stampLocal(),onSubmit:async value=>this.commitCompletion(n,true,value)});
     modal.open();return;
   }
   await this.commitCompletion(n,false,'');
 }
 async commitCompletion(n,checked,completedAt){
   if(this.busy)return;this.busy=true;
   try{const f=this.app.vault.getAbstractFileByPath(n.file.path);if(!(f instanceof TFile)||this.model.duplicates.has(n.id)){new Notice('項目 ID 重複，已阻止寫入');return;}
     await this.app.fileManager.processFrontMatter(f,fm=>{fm[this.plugin.settings.statusField]=checked?this.plugin.settings.doneValue:this.plugin.settings.activeValue;
       if(checked)fm[this.plugin.settings.completedAtField]=completedAt;else delete fm[this.plugin.settings.completedAtField];});
     await this.refresh();
   }catch(e){new Notice(`更新失敗：${e.message}`);}finally{this.busy=false;}
 }
 async changeCompletionDate(n,value){
   if(!this.isDone(n)){new Notice('請先標記完成');return;}
   try{await this.saveField(n,this.plugin.settings.completedAtField,value||stampLocal());}catch(e){new Notice(`日期更新失敗：${e.message}`);}
 }
 async reorderNode(moved,target,placement){
   if(!moved||!target)return;
   return this.reorderNodes([moved.id],target,placement);
 }
 async reorderNodes(ids,target,placement){
   if(this.busy||!target)return;
   let plan;
   try{plan=planReorder(this.model,ids,target.id,placement);}
   catch(e){new Notice(`無法換位：${e.message}`);return;}
   if(!plan.updates.length){new Notice('節點已位於該位置');return;}
   const originals=plan.updates.map(x=>({file:x.node.file,id:x.node.id,parent:x.node.parent||'',order:Number.isFinite(x.node.order)?x.node.order:null}));
   this.busy=true;
   const applied=[];
   try{
     for(const x of plan.updates){
       const f=this.app.vault.getAbstractFileByPath(x.node.file.path);
       if(!(f instanceof TFile))throw new Error(`找不到檔案：${x.node.file.path}`);
       await this.app.fileManager.processFrontMatter(f,fm=>{
         if(x.parent)fm['lmd-parent']=x.parent;else delete fm['lmd-parent'];
         fm[this.plugin.settings.orderField]=x.order;
       });
       applied.push(x.node.id);
     }
     // Update in-memory structure immediately. Waiting for a metadata-cache
     // refresh here caused successfully persisted order changes to appear undone.
     for(const x of plan.updates){
       this._pendingReorders.set(x.node.id,{parent:x.parent,order:x.order});
       x.node.parent=x.parent;x.node.order=x.order;
     }
     this.model=buildModel(this.nodes);
     if(this.tab==='map')this.drawMap();else this.render();
     if(plan.moved.length>1){this.multiSelected=new Set(plan.moved.map(n=>n.id));}
     new Notice(`已調整 ${plan.moved.length} 個分支的順序`);
   }catch(e){
     let rollbackFailures=0;
     const originalById=new Map(originals.map(x=>[x.id,x]));
     for(const id of applied.reverse()){
       const prev=originalById.get(id);
       try{await this.app.fileManager.processFrontMatter(prev.file,fm=>{
         if(prev.parent)fm['lmd-parent']=prev.parent;else delete fm['lmd-parent'];
         if(prev.order===null)delete fm[this.plugin.settings.orderField];else fm[this.plugin.settings.orderField]=prev.order;
       });}catch(_){rollbackFailures++;}
     }
     new Notice(`換位失敗，已嘗試復原${rollbackFailures?`（${rollbackFailures} 項需手動檢查）`:''}：${e.message}`);
   }finally{
     this.busy=false;
     // Do not read stale metadata immediately: metadataCache.changed triggers
     // a later refresh; the pending overlay keeps committed changes visible.
     if(!applied.length||applied.length!==plan.updates.length)await this.refresh();
   }
 }
 async setParent(n,newParent){if(!n || this.model.duplicates.has(n.id) || (newParent && (this.model.duplicates.has(newParent) || !this.model.byId.has(newParent))) || (newParent && isDescendant(newParent,n.id,this.model.byId))){new Notice('父子關係無效或 ID 重複，未修改');return;}try{await this.saveField(n,'lmd-parent',newParent||null);}catch(e){new Notice(`更新失敗：${e.message}`);}}
 async addNode(parentId=''){
   const source=await this.databaseSource();const folder=source.folder?.path||'';const target=source.folder;
   if(!(target instanceof TFolder)){new Notice(source.error||'請先指定規劃資料庫');return;}
   if(parentId && (!this.model.byId.has(parentId)||this.model.duplicates.has(parentId))){new Notice('父節點不存在或 ID 重複');return;}
   new TextPrompt(this.app,{title:parentId?'新增子節點':'新增根節點',label:'節點名稱',onSubmit:async title=>{
     const name=sanitizeName(title);let path=normalizePath(folder?`${folder}/${name}.md`:`${name}.md`);let i=2;
     while(this.app.vault.getAbstractFileByPath(path)){path=normalizePath(folder?`${folder}/${name} ${i++}.md`:`${name} ${i++}.md`);}
     const id=uid();const pageField=this.plugin.settings.pageField;const parentPage=parentId?this.model.byId.get(parentId)?.page:'';const pageValue=parentPage||(this.page!=='__all__'?this.page:'');const pageYaml=pageField&&pageValue?`${JSON.stringify(pageField)}: ${JSON.stringify(pageValue)}\n`:'';try{const note=await this.app.vault.create(path,`---\nlmd-id: ${id}\n${parentId?`lmd-parent: ${parentId}\n`:''}${JSON.stringify(this.plugin.settings.kindField)}: ${parentId?'任務':'方向'}\n${pageYaml}---\n\n`);this.selected=id;this.focus='';this.tab='map';await this.refresh();new Notice('已新增 Markdown 節點');}catch(e){new Notice(`新增失敗：${e.message}`);}
   }}).open();
 }
 async rename(n){new TextPrompt(this.app,{title:'重新命名',label:'檔案／節點名稱',value:n.file.basename,onSubmit:async name=>{try{const dest=normalizePath(`${folderOf(n.file.path)?folderOf(n.file.path)+'/':''}${sanitizeName(name)}.md`);if(dest!==n.file.path && this.app.vault.getAbstractFileByPath(dest)){new Notice('已有同名檔案');return;}await this.app.fileManager.renameFile(n.file,dest);await this.refresh();}catch(e){new Notice(`重新命名失敗：${e.message}`);}}}).open();}
 async dateChange(n,value){try{await this.saveField(n,this.plugin.settings.dateField,value||null);}catch(e){new Notice(`日期更新失敗：${e.message}`);}}
 getPageNames(){if(!this.plugin.settings.pageField)return [];const present=this.nodes.map(n=>n.page||'未分組');const field=this.dbSchema.find(f=>f.id===this.plugin.settings.pageField);const defined=Array.isArray(field?.options)?field.options.map(x=>typeof x==='string'?x:x?.name||x?.value||x?.label).filter(Boolean):[];return [...new Set([...defined,...present])].sort((a,b)=>{const order=this.plugin.settings.pageOrder||[];const ai=order.indexOf(a),bi=order.indexOf(b);return (ai<0?1e9:ai)-(bi<0?1e9:bi)||a.localeCompare(b,'zh-Hant');});}
 pageNodes(){if(this.page==='__all__'||!this.plugin.settings.pageField)return this.nodes;return this.nodes.filter(n=>(n.page||'未分組')===this.page);}
 changePage(page){this.pageCameras.set(this.page,{pan:{...this.mapPan},scale:this.mapScale,initialized:this.mapPanInitialized});this.page=page;const state=this.pageCameras.get(page);this.mapPan=state?{...state.pan}:{x:28,y:24};this.mapScale=state?.scale||1;this.mapPanInitialized=!!state?.initialized;this.focus='';this.selected='';this.render();}
 render(){const root=this.containerEl.children[1];if(!root)return;root.empty();root.addClass('vp-root','vp-v02','vp-v03');
   const head=el(root,'div','vp-head');const brand=el(head,'div','vp-brand');el(brand,'strong','', 'Visual Planner');el(brand,'span','vp-muted',`${this.nodes.length} 個節點`);
   const tabs=el(head,'div','vp-tabs');for(const [t,label] of [['map','心智圖'],['today','今日任務'],['calendar','日曆']]){const b=btn(tabs,label,()=>{this.tab=t;this.render();},this.tab===t?'vp-current':'');b.setAttribute('aria-pressed',String(this.tab===t));}
   const actions=el(head,'div','vp-head-actions');btn(actions,'＋ 新節點',()=>this.addNode(),'mod-cta');btn(actions,'↻',()=>this.refresh()).title='重新讀取';
   const body=el(root,'div','vp-body');if(this.source?.error){el(body,'div','vp-issue',this.source.error);btn(body,'開啟插件設定',()=>this.app.setting?.openTabById?.(this.plugin.manifest.id));return;}
   if(this.tab==='map')this.renderMap(body);else if(this.tab==='today')this.renderToday(body);else if(this.tab==='calendar')this.renderCalendar(body);else this.renderDiagnostics(body);
 }
 renderMap(body){
   const top=el(body,'div','vp-toolbar vp-map-toolbar');
   const pageField=this.plugin.settings.pageField;
   if(pageField){
     const pageBar=el(top,'div','vp-page-bar');
     const pages=[{value:'__all__',label:'全部'},...this.getPageNames().map(x=>({value:x,label:x}))];
     for(const item of pages){const b=btn(pageBar,item.label,()=>this.changePage(item.value),this.page===item.value?'vp-page-active':'');b.title=`切換到 ${item.label}`;
       if(item.value!=='__all__'){
         b.draggable=true;
         b.addEventListener('dragstart',e=>{e.dataTransfer.setData('application/x-vp-page',item.value);e.dataTransfer.effectAllowed='move';});
         b.addEventListener('dragover',e=>{if(e.dataTransfer.types.includes('application/x-vp-page')){e.preventDefault();b.addClass('vp-page-drop');}});
         b.addEventListener('dragleave',()=>b.removeClass('vp-page-drop'));
         b.addEventListener('drop',async e=>{e.preventDefault();b.removeClass('vp-page-drop');const from=e.dataTransfer.getData('application/x-vp-page');if(!from||from===item.value)return;
           const names=this.getPageNames().filter(x=>x!==from);names.splice(names.indexOf(item.value),0,from);this.plugin.settings.pageOrder=names;await this.plugin.saveSettings();this.render();});
       }
     }
   } else {const p=el(top,'span','vp-muted vp-page-hint','尚未設定分頁欄位');p.title='到插件設定，選擇資料庫的單選欄位';}
   const tools=el(top,'div','vp-map-tools');
   const search=tools.createEl('input',{type:'search',placeholder:'搜尋／聚焦',cls:'vp-search'});search.value=this.filter;search.title='搜尋目前分頁中的節點';search.addEventListener('input',()=>{this.filter=search.value;this.drawMap();});
   const choose=el(tools,'select','vp-focus');choose.createEl('option',{text:'全部分支',value:''});
   for(const n of this.pageNodes().slice().sort((a,b)=>a.file.basename.localeCompare(b.file.basename,'zh-Hant')))choose.createEl('option',{text:n.file.basename,value:n.id});
   choose.value=this.focus;choose.addEventListener('change',()=>{this.focus=choose.value;this.mapPanInitialized=false;this.drawMap();});
   btn(tools,'◎',()=>{if(this.selected){this.focus=this.selected;this.mapPanInitialized=false;this.drawMap();}},'vp-icon-btn').title='聚焦選取';
   btn(tools,'⌂',()=>{this.focus='';this.mapPanInitialized=false;this.drawMap();},'vp-icon-btn').title='返回全局並歸位';
   btn(tools,'−',()=>{this.mapScale=Math.max(.4,Math.round((this.mapScale-.1)*10)/10);this.updateCamera();},'vp-icon-btn').title='縮小';
   btn(tools,'+',()=>{this.mapScale=Math.min(2.4,Math.round((this.mapScale+.1)*10)/10);this.updateCamera();},'vp-icon-btn').title='放大';
   btn(tools,'▦',()=>{const f=this.source?.database;if(f)this.app.workspace.getLeaf('tab').openFile(f);},'vp-icon-btn').title='在新分頁開啟規劃 Database';
   btn(tools,this.detailsOpen?'收起詳情':'詳情',()=>{this.detailsOpen=!this.detailsOpen;this.render();},'vp-detail-toggle').title='選取節點後按 Space 切換詳情';
   btn(tools,this.plugin.settings.compactMode?'一般':'緊密',async()=>{this.plugin.settings.compactMode=!this.plugin.settings.compactMode;await this.plugin.saveSettings();this.drawMap();this.render();},'vp-icon-btn').title='切換節點密度';
   this.mapStatus=el(tools,'span','vp-muted vp-status','');
   const layout=el(body,'div',`vp-layout vp-map-layout ${this.detailsOpen?'vp-has-details':''}`);
   this.mapViewport=el(layout,'div','vp-map-viewport');this.mapViewport.tabIndex=0;
   // Infinite canvas: transform-based camera, independent of scroll offsets.
   let pan=null,marquee=null;
   this.mapViewport.addEventListener('pointerdown',e=>{
     const blank=!e.target.closest('.vp-map-card,button,input,select,textarea');
     if(e.button===0&&blank){
       const r=this.mapViewport.getBoundingClientRect();marquee={id:e.pointerId,x:e.clientX-r.left,y:e.clientY-r.top,cx:e.clientX-r.left,cy:e.clientY-r.top,add:e.ctrlKey||e.metaKey||e.shiftKey};
       marquee.rect=el(this.mapViewport,'div','vp-marquee');this.mapViewport.setPointerCapture(e.pointerId);e.preventDefault();return;
     }
     if(e.button!==2 && e.button!==1)return;
     pan={id:e.pointerId,x:e.clientX,y:e.clientY,originX:this.mapPan.x,originY:this.mapPan.y};
     try{this.mapViewport.setPointerCapture(e.pointerId);}catch(_){}
     this.mapViewport.addClass('vp-is-panning');e.preventDefault();
   });
   this.mapViewport.addEventListener('pointermove',e=>{
     if(marquee&&e.pointerId===marquee.id){const r=this.mapViewport.getBoundingClientRect();marquee.cx=e.clientX-r.left;marquee.cy=e.clientY-r.top;const box=marquee.rect;box.style.left=`${Math.min(marquee.x,marquee.cx)}px`;box.style.top=`${Math.min(marquee.y,marquee.cy)}px`;box.style.width=`${Math.abs(marquee.cx-marquee.x)}px`;box.style.height=`${Math.abs(marquee.cy-marquee.y)}px`;return;}
     if(!pan||e.pointerId!==pan.id)return;
     this.mapPan.x=pan.originX+e.clientX-pan.x;
     this.mapPan.y=pan.originY+e.clientY-pan.y;
     this.updateCamera();e.preventDefault();
   });
   const finishPan=e=>{
     if(marquee&&e.pointerId===marquee.id){const m=marquee;marquee=null;m.rect?.remove();const r=this.mapViewport.getBoundingClientRect();const x1=Math.min(m.x,m.cx)+r.left,x2=Math.max(m.x,m.cx)+r.left,y1=Math.min(m.y,m.cy)+r.top,y2=Math.max(m.y,m.cy)+r.top;if(!m.add)this.multiSelected.clear();
       if(x2-x1>5||y2-y1>5){for(const card of this.mapViewport.querySelectorAll('.vp-map-card')){const b=card.getBoundingClientRect();if(b.right>=x1&&b.left<=x2&&b.bottom>=y1&&b.top<=y2)this.multiSelected.add(card.dataset.nodeId);}}
       this.selected=[...this.multiSelected].at(-1)||'';this.drawMap();this.renderBulkToolbar();this.renderDetails();return;}
     if(!pan||e.pointerId!==pan.id)return;pan=null;this.mapViewport.removeClass('vp-is-panning');};
   for(const type of ['pointerup','pointercancel','lostpointercapture'])this.mapViewport.addEventListener(type,finishPan);
   this.mapViewport.addEventListener('contextmenu',e=>e.preventDefault());
   this.mapViewport.addEventListener('click',e=>{if(e.target===this.mapViewport||e.target.closest('.vp-map-canvas,.vp-map-stage,.vp-map-lines')&&!e.target.closest('.vp-map-card')){if(!e.ctrlKey&&!e.metaKey&&!e.shiftKey){this.multiSelected.clear();this.selected='';this.drawMap();this.renderBulkToolbar();this.renderDetails();}}});
   this.mapViewport.addEventListener('wheel',e=>{
     e.preventDefault();
     const factor=e.deltaMode===1?16:e.deltaMode===2?this.mapViewport.clientHeight:1;
     if(e.ctrlKey){
       const old=this.mapScale;
       const next=Math.max(.4,Math.min(2.4,Math.round((old+(e.deltaY>0?-.1:.1))*100)/100));
       if(next===old)return;
       const rect=this.mapViewport.getBoundingClientRect(),ox=e.clientX-rect.left,oy=e.clientY-rect.top;
       this.mapPan.x=ox-(ox-this.mapPan.x)*next/old;
       this.mapPan.y=oy-(oy-this.mapPan.y)*next/old;
       this.mapScale=next;
       this.updateCamera();
     }else{
       this.mapPan.x-=(e.shiftKey && Math.abs(e.deltaX)<Math.abs(e.deltaY)?e.deltaY:e.deltaX)*factor;
       this.mapPan.y-=(e.shiftKey && Math.abs(e.deltaX)<Math.abs(e.deltaY)?0:e.deltaY)*factor;
       this.updateCamera();
     }
   },{passive:false});
   this.mapViewport.addEventListener('keydown',e=>{
     if(e.target!==this.mapViewport && e.target.closest('input,textarea,select'))return;
     const n=this.model.byId.get(this.selected);
     if(e.key==='Tab'&&n){e.preventDefault();this.addNode(n.id);}
     else if(e.key==='Enter'&&n){e.preventDefault();this.addNode(n.parent||'');}
     else if(e.code==='Space'&&!e.repeat){e.preventDefault();this.detailsOpen=!this.detailsOpen;this.render();}
     else if(e.key==='Escape'&&this.detailsOpen){e.preventDefault();this.detailsOpen=false;this.render();}
   });
   this.mapStage=null;this.detailHost=this.detailsOpen?el(layout,'div','vp-detail'):null;this.bulkHost=el(body,'div','vp-bulk-toolbar');this.drawMap();this.renderDetails();this.renderBulkToolbar();
 }
 matchingIds(){const q=this.filter.toLocaleLowerCase().trim();if(!q)return null;const keep=new Set();for(const n of this.pageNodes()){if(!`${n.file.basename} ${n.kind} ${n.status}`.toLocaleLowerCase().includes(q))continue;let cursor=n.id;const seen=new Set();while(cursor&&!seen.has(cursor)){keep.add(cursor);seen.add(cursor);cursor=this.model.byId.get(cursor)?.parent;}}return keep;}
 updateCamera(){
   if(this.mapStage)this.mapStage.style.transform=`translate(${this.mapPan.x}px, ${this.mapPan.y}px) scale(${this.mapScale})`;
 }
 selectNode(id,e){
   const ctrl=!!(e?.ctrlKey||e?.metaKey),shift=!!e?.shiftKey;
   if(shift && this.selectionAnchor && this.visibleOrder.includes(this.selectionAnchor) && this.visibleOrder.includes(id)){
     const a=this.visibleOrder.indexOf(this.selectionAnchor),b=this.visibleOrder.indexOf(id);
     const ids=this.visibleOrder.slice(Math.min(a,b),Math.max(a,b)+1);
     if(!ctrl)this.multiSelected.clear();for(const selectedId of ids)this.multiSelected.add(selectedId);
   }else if(ctrl){if(this.multiSelected.has(id))this.multiSelected.delete(id);else this.multiSelected.add(id);this.selectionAnchor=id;}
   else{this.multiSelected=new Set([id]);this.selectionAnchor=id;}
   this.selected=id;this.drawMap();this.renderDetails();this.renderBulkToolbar();this.mapViewport?.focus({preventScroll:true});
 }
 renderBulkToolbar(){if(!this.bulkHost)return;this.bulkHost.empty();const ids=[...this.multiSelected].filter(id=>this.model.byId.has(id)&&!this.model.duplicates.has(id));if(ids.length<2)return;
   el(this.bulkHost,'strong','',`已選取 ${ids.length} 個節點`);
   btn(this.bulkHost,'安排日期',()=>{new DatePrompt(this.app,{title:`批量安排 ${ids.length} 個項目`,value:`${todayLocal()}T00:00`,onSubmit:async value=>{const date=value.slice(0,10);await this.bulkWrite(ids,fm=>{fm[this.plugin.settings.dateField]=date;});}}).open();});
   btn(this.bulkHost,'標記完成',()=>{new DatePrompt(this.app,{title:`批量完成 ${ids.length} 個項目`,value:stampLocal(),onSubmit:async value=>{await this.bulkWrite(ids,fm=>{fm[this.plugin.settings.statusField]=this.plugin.settings.doneValue;fm[this.plugin.settings.completedAtField]=value;});}}).open();});
   btn(this.bulkHost,'清除選取',()=>{this.multiSelected.clear();this.selected='';this.drawMap();this.renderBulkToolbar();this.renderDetails();});
 }
 async bulkWrite(ids,update){if(this.busy)return;this.busy=true;let done=0;try{for(const id of ids){const n=this.model.byId.get(id);if(!n)continue;const file=this.app.vault.getAbstractFileByPath(n.file.path);if(!(file instanceof TFile))continue;await this.app.fileManager.processFrontMatter(file,update);done++;}new Notice(`已更新 ${done} 個節點`);}catch(e){new Notice(`批量更新中止，已更新 ${done} 個：${e.message}`);}finally{this.busy=false;await this.refresh();}}
 drawMap(){if(!this.mapViewport)return;
   const viewport=this.mapViewport;
   viewport.empty();this._nodeDropTarget=null;
   const pageNodes=this.pageNodes(), pageModel=buildModel(pageNodes);this.activeModel=pageModel;const keep=this.matchingIds(), roots=this.focus?[pageModel.byId.get(this.focus)].filter(Boolean):pageModel.roots;
   if(!roots.length){el(this.mapViewport,'div','vp-empty','這個資料庫沒有可顯示的根節點。可先新增一個方向。');return;}
   const visible=[], children=new Map(), seen=new Set();
   const visit=(node,depth)=>{if(!node||seen.has(node.id)||depth>40||(keep&&!keep.has(node.id)))return;seen.add(node.id);visible.push({node,depth});
      const cs=(pageModel.children.get(node.id)||[]).filter(n=>!keep||keep.has(n.id));
      if(!this.collapsed.has(node.id)||keep){children.set(node.id,cs);for(const c of cs)visit(c,depth+1);}else children.set(node.id,[]);
   };for(const r of roots)visit(r,0);
   if(!visible.length){el(this.mapViewport,'div','vp-empty','沒有符合搜尋的節點');return;}
   
   const compact=!!this.plugin.settings.compactMode;
   const w=compact?178:214, nameFont=compact?12:14;
   const hSetting=Number(this.plugin.settings.horizontalGap);
   const vSetting=Number(this.plugin.settings.verticalGap);
   const hGap=Math.max(8,Math.min(180,Number.isFinite(hSetting)?hSetting:42));
   const vGap=Math.max(0,Math.min(120,Number.isFinite(vSetting)?vSetting:12));
   const xGap=w+hGap;
   const sizes=new Map();
   for(const {node} of visible){
     const name=node.file.basename;
     // Conservative CJK/Latin width estimate: leave enough room for fold/add handles.
     let units=0;for(const ch of name)units+=ch.charCodeAt(0)>255?1:0.57;
     const charsPerLine=compact?14:15;
     const lines=Math.max(1,Math.ceil(units/charsPerLine));
     const h=compact?Math.max(29,10+lines*16):Math.max(44,22+lines*19);
     sizes.set(node.id,{w,h});
   }
   let cursorY=34;const xy=new Map();
   const position=(n,depth)=>{const cs=children.get(n.id)||[],size=sizes.get(n.id);let y;
     if(!cs.length){y=cursorY;cursorY+=size.h+vGap;}
     else{for(const c of cs)position(c,depth+1);const first=cs[0],last=cs[cs.length-1];const mid=(xy.get(first.id).y+sizes.get(first.id).h/2+xy.get(last.id).y+sizes.get(last.id).h/2)/2;y=mid-size.h/2;}
     xy.set(n.id,{x:depth*xGap+45,y});};
   for(const r of roots)if(seen.has(r.id))position(r,0);
   this.visibleOrder=visible.slice().sort((a,b)=>xy.get(a.node.id).y-xy.get(b.node.id).y).map(v=>v.node.id);
   const maxDepth=Math.max(...visible.map(a=>a.depth));
   const mapW=Math.max(700,(maxDepth+1)*xGap+w+100),mapH=Math.max(380,cursorY+75);
   const canvas=el(this.mapViewport,'div','vp-map-canvas');
   const stage=el(canvas,'div','vp-map-stage');
   this.mapStage=stage;
   stage.style.width=`${mapW}px`;stage.style.height=`${mapH}px`;
   if(!this.mapPanInitialized){this.mapPan={x:28,y:24};this.mapPanInitialized=true;}
   this.updateCamera();
   const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.setAttribute('width',String(mapW));svg.setAttribute('height',String(mapH));svg.setAttribute('class','vp-map-lines');stage.appendChild(svg);
   const svgNS='http://www.w3.org/2000/svg';
   for(const {node} of visible){if(!seen.has(node.parent))continue;const p=xy.get(node.parent),c=xy.get(node.id);if(!p||!c)continue;
     const path=document.createElementNS(svgNS,'path');const x1=p.x+w,y1=p.y+sizes.get(node.parent).h/2,x2=c.x,y2=c.y+sizes.get(node.id).h/2;path.setAttribute('d',`M ${x1} ${y1} C ${x1+65} ${y1}, ${x2-65} ${y2}, ${x2} ${y2}`);path.setAttribute('class','vp-map-edge');svg.appendChild(path);
   }
   for(const {node,depth} of visible){const c=xy.get(node.id);const card=el(stage,'div',`vp-map-card ${this.selected===node.id?'vp-map-selected':''} ${depth===0?'vp-map-root':''} ${this.isDone(node)?'vp-map-completed':''} ${this.multiSelected.has(node.id)?'vp-map-multi-selected':''} ${compact?'vp-map-compact':''}`);
     card.dataset.nodeId=node.id;card.style.left=`${c.x}px`;card.style.top=`${c.y}px`;card.style.width=`${w}px`;card.style.height=`${sizes.get(node.id).h}px`;
     // Native HTML drag-and-drop is intentionally disabled: it was racing with
     // multi-selection and Obsidian's pointer handlers. Pointer drag is scoped
     // to the visual map only; right/middle buttons continue to pan the canvas.
     card.draggable=false;
     let gesture=null;
     const clearTarget=()=>{
       if(this._nodeDropTarget){this._nodeDropTarget.removeClass('vp-map-drop');delete this._nodeDropTarget.dataset.dropPlacement;this._nodeDropTarget=null;}
       this._mapInsertionGuide?.remove();this._mapInsertionGuide=null;this._nodeDropPlacement=null;
     };
     // Capture immediately. Capturing only AFTER passing the movement threshold
     // loses the drag when the pointer exits a small card in one movement frame.
     card.addEventListener('pointerdown',e=>{
       if(e.button!==0||e.target.closest('button,input,select,textarea')||this.busy)return;
       gesture={id:e.pointerId,startX:e.clientX,startY:e.clientY,dragging:false};
       try{card.setPointerCapture(e.pointerId);}catch(_){}
     });
     // The card body is exclusively a PARENT drop target. Reordering happens
     // only on the insertion guide just OUTSIDE a card; never by hovering over
     // its upper/lower portions. This matches the user's original interaction.
     const dropAt=(x,y)=>findMapDropTarget(
       [...this.mapViewport.querySelectorAll('.vp-map-card')].filter(other=>other!==card),
       x,y
     );
     const showDrop=(found)=>{
       clearTarget();
       if(!found)return;
       if(found.placement==='inside'){
         found.other.dataset.dropPlacement='inside';
         found.other.addClass('vp-map-drop');
         this._nodeDropTarget=found.other;
       }else{
         this._nodeDropTarget=found.other;
         this._nodeDropPlacement=found.placement;
         // The guide is drawn in screen-space relative to the viewport, so its
         // location stays correct at any pan or zoom level.
         const viewportRect=this.mapViewport.getBoundingClientRect();
         const line=el(this.mapViewport,'div','vp-map-insertion-guide');
         const r=found.rect;
         line.style.left=`${r.left-viewportRect.left-10}px`;
         line.style.top=`${(found.placement==='before'?r.top:r.bottom)-viewportRect.top-2}px`;
         line.style.width=`${r.width+20}px`;
         this._mapInsertionGuide=line;
       }
     };
     card.addEventListener('pointermove',e=>{
       if(!gesture||gesture.id!==e.pointerId)return;
       if(!gesture.dragging){
         if(Math.hypot(e.clientX-gesture.startX,e.clientY-gesture.startY)<7)return;
         gesture.dragging=true;
         card.addClass('vp-map-dragging');
       }
       showDrop(dropAt(e.clientX,e.clientY));
       e.preventDefault();
     });
     const endGesture=e=>{
       if(!gesture||gesture.id!==e.pointerId)return;
       const wasDragging=gesture.dragging;gesture=null;
       if(!wasDragging){
         try{if(card.hasPointerCapture(e.pointerId))card.releasePointerCapture(e.pointerId);}catch(_){}
         return;
       }
       this._skipNodeClicksUntil=Date.now()+350;
       // Re-evaluate at release. A target card -> parent change; a guide next
       // to a card -> order change, keeping its existing parent when same-level.
       const found=dropAt(e.clientX,e.clientY);
       const targetId=found?.other?.dataset.nodeId;
       const placement=found?.placement;
       clearTarget();card.removeClass('vp-map-dragging');
       try{if(card.hasPointerCapture(e.pointerId))card.releasePointerCapture(e.pointerId);}catch(_){}
       if(!targetId||targetId===node.id){
         if(!targetId)new Notice('請放到卡片本體以改父級，或放到旁邊的插入指示線以排序');
         return;
       }
       const targetNode=this.model.byId.get(targetId);
       if(!targetNode)return;
       const ids=(this.multiSelected.size>1&&this.multiSelected.has(node.id))?[...this.multiSelected]:[node.id];
       if(ids.length>1)void this.reorderNodes(ids,targetNode,placement);
       else void this.reorderNode(node,targetNode,placement);
       e.preventDefault();
     };
     card.addEventListener('pointerup',endGesture);
     card.addEventListener('pointercancel',e=>{if(gesture&&gesture.id===e.pointerId){gesture=null;clearTarget();card.removeClass('vp-map-dragging');}});
     card.addEventListener('click',e=>{if(Date.now()<(this._skipNodeClicksUntil||0)){e.preventDefault();e.stopPropagation();return;}this.selectNode(node.id,e);});
     card.addEventListener('dblclick',()=>void this.app.workspace.getLeaf(true).openFile(node.file));
     el(card,'div','vp-map-card-name',node.file.basename);
     if(!compact){const info=el(card,'div','vp-map-card-info');el(info,'span','',node.kind);if(node.date)el(info,'span','',node.date.slice(5,10));if(this.isDone(node))el(info,'span','vp-map-done','✓');}else if(this.isDone(node)){el(card,'span','vp-compact-done','✓');}
     const cs=pageModel.children.get(node.id)||[];
     if(cs.length){const fold=btn(card,this.collapsed.has(node.id)?`＋${cs.length}`:'−',e=>{},'vp-map-fold');fold.addEventListener('click',e=>{e.stopPropagation();if(this.collapsed.has(node.id))this.collapsed.delete(node.id);else this.collapsed.add(node.id);this.drawMap();});}
   }
   if(pageNodes.length>visible.length){el(this.mapViewport,'div','vp-map-tip',`顯示 ${visible.length} / ${pageNodes.length} 項`);}
   // Display live viewport geometry; a collapsed container must never fail silently.
   if(this.mapStatus){
     const status=this.mapStatus;
     const target=this.mapViewport;
     const count=visible.length;
     const update=()=>{
       if(!target.isConnected)return;
       const width=Math.round(target.getBoundingClientRect().width);
       const height=Math.round(target.getBoundingClientRect().height);
       status.setText(`${count} 項`+(width<80||height<80?' · 畫布過小':'') );
     };
     requestAnimationFrame(update);
   }
   // Avoid deferring camera application: the scene uses one CSS transform
   // and never relies on Obsidian's asynchronous scroll layout.

 }
 renderDetails(){if(!this.detailHost)return;this.detailHost.empty();btn(this.detailHost,'×',()=>{this.detailsOpen=false;this.render();},'vp-close-detail').title='關閉詳情';const node=this.nodes.find(n=>n.id===this.selected);if(!node){el(this.detailHost,'h3','', '節點詳情');el(this.detailHost,'p','vp-muted','點選左側節點，可在這裡安排日期、修改階層與開啟筆記。');return;}
   el(this.detailHost,'h3','',node.file.basename);el(this.detailHost,'div','vp-muted',node.file.path);const bar=el(this.detailHost,'div','vp-actions');btn(bar,'開啟筆記',()=>this.app.workspace.getLeaf(true).openFile(node.file));btn(bar,'更名',()=>this.rename(node));btn(bar,'新增子節點',()=>this.addNode(node.id));
   const siblings=((node.parent?this.model.children.get(node.parent):this.model.roots)||[]).filter(x=>!this.model.duplicates.has(x.id));
   const idx=siblings.findIndex(x=>x.id===node.id);
   const up=btn(bar,'↑ 上移',()=>{if(idx>0)void this.reorderNode(node,siblings[idx-1],'before');});up.disabled=idx<=0;
   const down=btn(bar,'↓ 下移',()=>{if(idx>=0&&idx<siblings.length-1)void this.reorderNode(node,siblings[idx+1],'after');});down.disabled=idx<0||idx>=siblings.length-1;
   if(this.plugin.settings.pageField){const pageLabel=el(this.detailHost,'label','vp-field');el(pageLabel,'span','','分頁');const pageSel=el(pageLabel,'select','');pageSel.createEl('option',{text:'未分組',value:''});for(const value of this.getPageNames().filter(x=>x!=='未分組'))pageSel.createEl('option',{text:value,value});pageSel.value=node.page||'';pageSel.addEventListener('change',()=>void this.saveField(node,this.plugin.settings.pageField,pageSel.value||null));}
   const kind=el(this.detailHost,'label','vp-field');el(kind,'span','', '節點類型');const kindSel=el(kind,'select','');for(const t of TYPES)kindSel.createEl('option',{text:t,value:t});if(!TYPES.includes(node.kind))kindSel.createEl('option',{text:node.kind,value:node.kind});kindSel.value=node.kind;kindSel.addEventListener('change',()=>void this.saveField(node,this.plugin.settings.kindField,kindSel.value));
   const parent=el(this.detailHost,'label','vp-field');el(parent,'span','', '父節點（同一規劃庫）');const select=el(parent,'select','');select.createEl('option',{text:'無／根節點',value:''});for(const n of [...this.model.byId.values()].sort((a,b)=>a.file.basename.localeCompare(b.file.basename,'zh-Hant'))){if(n.id===node.id||isDescendant(n.id,node.id,this.model.byId))continue;select.createEl('option',{text:n.file.basename,value:n.id});}select.value=node.parent;select.addEventListener('change',()=>void this.setParent(node,select.value));
   const label=el(this.detailHost,'label','vp-field');el(label,'span','', '計畫執行日期');const date=el(label,'input','');date.type='date';date.value=/^\d{4}-\d{2}-\d{2}/.test(node.date)?node.date.slice(0,10):'';date.addEventListener('change',()=>void this.dateChange(node,date.value));
   const done=el(this.detailHost,'label','vp-check');const box=done.createEl('input',{type:'checkbox'});box.checked=this.isDone(node);box.addEventListener('change',()=>void this.setComplete(node,box.checked));done.createSpan({text:'標記完成（可選完成日期）'});
   if(this.isDone(node)){const finished=el(this.detailHost,'label','vp-field');el(finished,'span','','實際完成日期與時間');
     const completed=el(finished,'input','');completed.type='datetime-local';completed.value=node.completedAt?node.completedAt.replace(' ','T').slice(0,16):'';
     completed.addEventListener('change',()=>void this.changeCompletionDate(node,completed.value));}
   
   el(this.detailHost,'p','vp-tip','原始 Markdown 不會因為本視圖的篩選或排序而被移動。父子關係直接寫回 lmd-parent。');
 }
 renderToday(body){el(body,'p','vp-muted',`日期：${todayLocal()}。此頁只顯示 plan-date（或設定的日期欄位）等於今天且未完成的任務。`);
   const items=this.nodes.filter(n=>n.kind==='任務'&&n.date.slice(0,10)===todayLocal()&&!this.isDone(n));if(!items.length)el(body,'div','vp-empty','今天目前沒有排定的未完成任務。可以到「規劃樹」點選節點，指定今天的日期。');
   for(const n of items){const line=el(body,'div','vp-today-item');const check=line.createEl('input',{type:'checkbox'});check.addEventListener('change',()=>void this.setComplete(n,check.checked));const a=btn(line,n.file.basename,()=>{this.tab='map';this.selected=n.id;this.focus='';this.filter='';this.render();},'vp-today-name');el(line,'span','vp-muted',n.kind);}
   const completed=this.nodes.filter(n=>n.kind==='任務'&&n.completedAt.slice(0,10)===todayLocal()&&this.isDone(n));if(completed.length){el(body,'h3','vp-section-title','今日完成');for(const n of completed)el(body,'div','vp-done-item',`✓ ${n.file.basename}`);}
 }
 renderCalendar(body){
   const box=el(body,'div','vp-calendar-wrap');const toolbar=el(box,'div','vp-calendar-toolbar');
   btn(toolbar,'‹',()=>{const [y,m]=this.calendarMonth.split('-').map(Number);{const d=new Date(y,m-2,1);this.calendarMonth=`${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}`;}this.render();});
   el(toolbar,'strong','',this.calendarMonth.replace('-',' 年 ')+' 月');
   btn(toolbar,'›',()=>{const [y,m]=this.calendarMonth.split('-').map(Number);{const d=new Date(y,m,1);this.calendarMonth=`${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}`;}this.render();});
   btn(toolbar,'本月',()=>{this.calendarMonth=todayLocal().slice(0,7);this.render();});
   const mode=el(toolbar,'select','');for(const [v,label] of [['planned','計畫日期'],['completed','完成日期']])mode.createEl('option',{text:label,value:v});mode.value=this.calendarDateMode;mode.onchange=()=>{this.calendarDateMode=mode.value;this.render();};
   if(this.plugin.settings.pageField){const pages=el(toolbar,'select','');pages.createEl('option',{text:'全部 Page',value:'__all__'});for(const value of this.getPageNames())pages.createEl('option',{text:value,value});pages.value=this.calendarPage;pages.onchange=()=>{this.calendarPage=pages.value;this.render();};}
   const [year,month]=this.calendarMonth.split('-').map(Number);const grid=el(box,'div','vp-calendar-grid');
   for(const day of ['日','一','二','三','四','五','六'])el(grid,'div','vp-calendar-weekday',day);
   const start=new Date(year,month-1,1).getDay();const count=new Date(year,month,0).getDate();
   for(let i=0;i<start;i++)el(grid,'div','vp-calendar-empty');
   const filtered=this.nodes.filter(n=>this.calendarPage==='__all__'||(n.page||'未分組')===this.calendarPage);
   for(let d=1;d<=count;d++){
     const day=`${this.calendarMonth}-${String(d).padStart(2,'0')}`;
     const cell=el(grid,'div',`vp-calendar-day ${day===todayLocal()?'vp-calendar-today':''}`);el(cell,'div','vp-calendar-number',d);
     const items=filtered.filter(n=>(this.calendarDateMode==='planned'?n.date:n.completedAt).slice(0,10)===day);
     for(const n of items){const item=el(cell,'button',`vp-calendar-event ${this.isDone(n)?'vp-calendar-done':''}`,n.file.basename);item.title=n.file.basename+' · '+n.kind;
       item.draggable=this.calendarDateMode==='planned';item.addEventListener('dragstart',e=>{e.dataTransfer.setData('application/x-vp-node',n.id);});
       item.addEventListener('click',()=>{this.selected=n.id;this.tab='map';this.detailsOpen=true;this.focus=n.id;this.mapPanInitialized=false;this.render();});
     }
     if(this.calendarDateMode==='planned'){
       cell.addEventListener('dragover',e=>{if(e.dataTransfer.types.includes('application/x-vp-node')){e.preventDefault();cell.addClass('vp-calendar-drop');}});
       cell.addEventListener('dragleave',()=>cell.removeClass('vp-calendar-drop'));
       cell.addEventListener('drop',e=>{e.preventDefault();cell.removeClass('vp-calendar-drop');const id=e.dataTransfer.getData('application/x-vp-node');const n=this.model.byId.get(id);if(n)void this.dateChange(n,day);});
     }
   }
   el(box,'p','vp-muted','拖曳計畫日期中的任務到其他日子，只會修改計畫日期；完成日期必須在節點詳情中修改。');
 }
 renderDiagnostics(body){el(body,'h3','', '資料完整性檢查');el(body,'p','vp-muted','只掃描專用資料庫來源資料夾內、具有 lmd-id 的 Markdown；不會自動修正舊資料。');const warnings=this.model.warnings;if(!warnings.length)el(body,'div','vp-ok','目前讀取範圍沒有偵測到重複 ID、缺失父項或循環關係。');else for(const w of warnings)el(body,'div','vp-issue',w);
   el(body,'h3','vp-section-title','資料庫來源位置');el(body,'p','vp-muted','新節點只建立於選定 .database 的來源資料夾；外部研究筆記請在內文用 Obsidian 連結引用。');
   const defs=this.app.vault.getFiles().filter(f=>f.extension==='database');if(!defs.length)el(body,'p','vp-muted','找不到 .database 檔案。');else for(const f of defs.slice(0,50))el(body,'div','vp-db-entry',f.path);
 }
}
class PlannerSettings extends PluginSettingTab{
 constructor(app,plugin){super(app,plugin);this.plugin=plugin;}
 display(){const containerEl=this.containerEl;containerEl.empty();
  new Setting(containerEl).setName('專用規劃資料庫').setDesc('選擇唯一的 .database；必須是單一資料夾來源。只讀取該資料夾的直屬 Markdown，不載入其他知識庫。').addDropdown(drop=>{
    drop.addOption('','請選擇 .database');for(const f of this.app.vault.getFiles().filter(f=>f.extension==='database').sort((a,b)=>a.path.localeCompare(b.path)))drop.addOption(f.path,f.path);
    drop.setValue(this.plugin.settings.databasePath||'');drop.onChange(async v=>{this.plugin.settings.databasePath=v;await this.plugin.saveSettings();for(const leaf of this.app.workspace.getLeavesOfType(VIEW))await leaf.view.refresh();});
  });
  new Setting(containerEl).setName('分頁欄位').setDesc('使用本規劃 .database 的單選屬性建立 Page；不建立額外資料庫。未分類的筆記會歸入「未分組」。').addDropdown(drop=>{drop.addOption('','不啟用分頁');const dbFile=this.app.vault.getAbstractFileByPath(this.plugin.settings.databasePath);if(dbFile instanceof TFile){void this.app.vault.read(dbFile).then(raw=>{let def;try{def=JSON.parse(raw);}catch(_){return;}for(const field of (Array.isArray(def.schema)?def.schema:[]).filter(x=>x.type==='single-select'))drop.addOption(field.id,`${field.name||field.id} (${field.id})`);drop.setValue(this.plugin.settings.pageField||'');}).catch(()=>{});}if(this.plugin.settings.pageField)drop.addOption(this.plugin.settings.pageField,this.plugin.settings.pageField+'（目前選取）');drop.setValue(this.plugin.settings.pageField||'');drop.onChange(async v=>{this.plugin.settings.pageField=v;await this.plugin.saveSettings();for(const leaf of this.app.workspace.getLeavesOfType(VIEW))await leaf.view.refresh();});});
  new Setting(containerEl).setName('心智圖顯示密度').setDesc('緊密模式只顯示節點名稱與完成狀態；更適合大量分支。').addToggle(toggle=>toggle.setValue(!!this.plugin.settings.compactMode).onChange(async value=>{this.plugin.settings.compactMode=value;await this.plugin.saveSettings();for(const leaf of this.app.workspace.getLeavesOfType(VIEW))leaf.view?.render?.();}));
  const gapControl=(key,title,description,max)=>new Setting(containerEl).setName(title).setDesc(description)
    .addSlider(slider=>slider.setLimits(0,max,2).setDynamicTooltip().setValue(Number(this.plugin.settings[key])||0).onChange(async value=>{this.plugin.settings[key]=value;await this.plugin.saveSettings();for(const leaf of this.app.workspace.getLeavesOfType(VIEW))if(leaf.view?.tab==='map')leaf.view.drawMap();}))
    .addExtraButton(button=>button.setIcon('reset').setTooltip('恢復建議間距').onClick(async()=>{this.plugin.settings[key]=key==='verticalGap'?12:42;await this.plugin.saveSettings();this.display();for(const leaf of this.app.workspace.getLeavesOfType(VIEW))if(leaf.view?.tab==='map')leaf.view.drawMap();}));
  gapControl('verticalGap','心智圖垂直間距','相鄰節點的垂直距離（0–100 px）；調整後立即更新畫布。',100);
  gapControl('horizontalGap','心智圖水平間距','父子分支的水平距離（0–160 px）；調整後立即更新畫布。',160);
  for(const [key,label,desc] of [['statusField','任務狀態欄位','預設 plan-status；如果舊庫使用 V，可設成 V'],['doneValue','完成狀態的值','預設 已完成'],['activeValue','取消完成時的值','預設 進行中'],['dateField','執行日期欄位','預設 plan-date'],['kindField','節點類型欄位','預設 plan-type'],['completedAtField','完成時間欄位','預設 plan-completed-at']])new Setting(containerEl).setName(label).setDesc(desc).addText(input=>input.setValue(this.plugin.settings[key]).onChange(async v=>{if(!v.trim())return;this.plugin.settings[key]=v.trim();await this.plugin.saveSettings();}));
 }
}
module.exports=class VisualPlannerPlugin extends Plugin{
 async onload(){this.settings=Object.assign({},DEFAULTS,await this.loadData());this.registerView(VIEW,leaf=>new PlannerView(leaf,this));this.addRibbonIcon('git-fork','開啟視覺規劃',()=>this.activate());this.addCommand({id:'open-visual-planner',name:'開啟視覺規劃',callback:()=>this.activate()});this.addCommand({id:'planner-data-diagnostics',name:'檢查規劃資料完整性',callback:async()=>{await this.activate();const leaf=this.app.workspace.getLeavesOfType(VIEW)[0];if(leaf?.view){leaf.view.tab='diagnostics';leaf.view.render();}}});this.addSettingTab(new PlannerSettings(this.app,this));
   const requestRefresh=()=>{if(this._refreshTimer)clearTimeout(this._refreshTimer);this._refreshTimer=setTimeout(()=>{for(const leaf of this.app.workspace.getLeavesOfType(VIEW)){if(!leaf.view?.busy)void leaf.view?.refresh?.();}},250);};
   this.registerEvent(this.app.vault.on('create',requestRefresh));this.registerEvent(this.app.vault.on('delete',requestRefresh));this.registerEvent(this.app.vault.on('rename',requestRefresh));this.registerEvent(this.app.metadataCache.on('changed',requestRefresh));
 }
 async saveSettings(){await this.saveData(this.settings);}
 async activate(){let leaf=this.app.workspace.getLeavesOfType(VIEW)[0];if(!leaf){leaf=this.app.workspace.getLeaf('tab');await leaf.setViewState({type:VIEW,active:true});}this.app.workspace.revealLeaf(leaf);}
 onunload(){if(this._refreshTimer)clearTimeout(this._refreshTimer);}
};
