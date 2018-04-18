% --------------  Section 2: ACTION MODEL   

% -------------- 2.1.1 Planning Context 

% -------------- Domains 

time(1..7).
sim(0).
agent(paul;driver).
victim(driver).
positiveFluent(noMedic;alive(D);keptAlive(D);safe(D);treatment(D);needRehab(D)):-victim(D).
nonInertial(alive(D);keptAlive(D);safe(D);treatment(D);needRehab(D)):-victim(D).
priority(A,U):-action(A),auto(U).
capable(paul,call;aid(driver);safety(driver)).
capable(driver,rehab).

% -------------- Initial Situation  

initially(alive(driver)).
initially(neg(safe(driver))).
initially(noMedic).

% -------------- Event Specification  

% Act: aid
actName(aid(driver)).
prec(alive(D2),act(D1,aid(D2))):-agent(D1),victim(D2).
effect(act(D1,aid(D2)),keptAlive(D2)):-agent(D1),victim(D2).

% Act: safety 
actName(safety(driver)).
prec(keptAlive(D2),act(D1,safety(D2))):-agent(D1),victim(D2).
effect(act(D1,safety(D2)),safe(D2)):-agent(D1),victim(D2).

% Act: call
actName(call).
prec(noMedic,act(D1,call)):-agent(D1).
prec(safe(D2),act(D1,call)):-agent(D1),victim(D2).
effect(act(D1,call),treatment(D2)):-agent(D1),victim(D2).
effect(act(D1,call),neg(noMedic)):-agent(D1).

% Act: rehab
actName(rehab).
prec(neg(treatment(D)),act(D,rehab)):-victim(D).
prec(needRehab(D),act(D,rehab)):-victim(D).
effect(act(D,rehab),treatment(D)):-victim(D).

% Auto: part recovery
auto(partRecovery(D)):-victim(D).
prec(safe(D),partRecovery(D)):-victim(D).
prec(neg(treatment(D)),partRecovery(D)):-victim(D).
effect(partRecovery(D),needRehab(D)):-victim(D).

% Auto: full recovery
auto(fullRecovery(D)):-victim(D).
prec(treatment(D),fullRecovery(D)):-victim(D).

% ------------ 2.1.2 Modelling Actions 

event(U):-auto(U).
event(I):-volition(I).
volition(A):-action(A).
volition(O):-omission(O).
fluent(F;neg(F)):-positiveFluent(F).

action(act(D,X)):-actName(X),agent(D),capable(D,X).
holds(S,F,1):-initially(F),sim(S).
holds(S,F,T+1):-occurs(S,E,T),effect(E,F),positiveFluent(F).
holds(S,F,T+1):-holds(S,F,T),{occurs(S,E,T):effect(E,neg(F))}0,not nonInertial(F),time(T).
possible(S,E,T):-complete(S,E,T),event(E),not action(E). 
possible(S,A,T):-complete(S,A,T),performs(S,A,T),action(A).
overtaken(S,E1,T):-possible(S,E1,T),possible(S,E2,T),priority(E2,E1),E1!=E2. 		
occurs(S,E,T):-possible(S,E,T),not overtaken(S,E,T).
holds(S,neg(F),T):-not holds(S,F,T),sim(S),positiveFluent(F),time(T).

% ------------ 2.2 Modelling Omissions 

omission(omit(D,X)):-action(act(D,X)).
complete(S,U,T):-{not holds(S,F,T):prec(F,U)}0,sim(S),auto(U),time(T).
complete(S,act(D,X),T):-{not holds(S,F,T):prec(F,act(D,X))}0,not occurs(S,omit(D,X),T-1),sim(S),action(act(D,X)),time(T).
repeat(S,omit(D,X),T2):-occurs(S,omit(D,X),T1),complete(S,act(D,X),T2),T1<T2.
complete(S,omit(D,X),T):-complete(S,act(D,X),T),not performs(S,act(D,X),T),not overtaken(S,act(D,X),T),not repeat(S,omit(D,X),T).
priority(omit(D,X),E):-priority(act(D,X),E).
holds(S,F,T+1):-occurs(S,omit(D,X),T),holds(S,F,T),nonInertial(F).
effect(omit(D,X),F):-effect(act(D,X),neg(F)).
effect(omit(D,X),neg(F)):-effect(act(D,X),F),positiveFluent(F).

% ------------ 2.4 Generating a Plan 

0{performs(0,A,T):action(A)}1:-time(T).
:-performs(0,A,T),not complete(0,A,T).	
:-noGood(0).

good(fullRecovery(D);partRecovery(D)):-victim(D).
someGood(0):-canArise(0,E),good(E).
noGood(0):-not someGood(0).

% ---------- Section 3: EVENT-BASED CAUSALITY  

% ------------ 3.1 Supporting causality 

posRel(causes;enables).
r(S,causes,E,T,F):-occurs(S,E,T),effect(E,F),holds(S,F,T+1).
r(S,causes,F,T,U):-holds(S,F,T),prec(F,U),occurs(S,U,T),auto(U).
r(S,R,E1,T1,E2):-r(S,causes,E1,T1,C),r(S,R,C,T2,E2),event(E1;E2),T2>T1,posRel(R).
r(S,enables,F,T,A):-holds(S,F,T),prec(F,A),occurs(S,A,T),action(A).
r(S,enables,F,T,omit(D,X)):-holds(S,F,T),prec(F,act(D,X)),occurs(S,omit(D,X),T).

% ------------ 3.2 Opposing causality 

hyp(F1,F2):-prec(F1,U),auto(U),effect(U,F2).
hyp(F1,F3):-hyp(F1,F2),hyp(F2,F3).
canArise(S,E):-occurs(S,E,T).
canArise(S,omit(D,X)):-occurs(S,act(D,X),T).
canArise(S,act(D,X)):-occurs(S,omit(D,X),T).
transTerm(S,E,F,T):-occurs(S,E,T),effect(E,neg(F)).
transTerm(S,E,F2,T):-transTerm(S,E,F1,T),hyp(F1,F2),positiveFluent(F2).
irrelevant(S,E1,T1,E2,T2):-transTerm(S,E1,F1,T1),prec(F1,E2),prec(F2,E2),not holds(S,F2,T2),not transTerm(S,E1,F2,T1),T2>T1,time(T2).
relevant(S,E1,T1,E2):-transTerm(S,E1,F1,T1),not irrelevant(S,E1,T1,E2,T2),T2>T1,time(T2),event(E2). 

negRel(prevents;excludes).
r(S,prevents,E,T,U):-transTerm(S,E,F,T),prec(F,U),relevant(S,E,T,U),not canArise(S,U),auto(U).
r(S,excludes,E,T,A):-transTerm(S,E,F,T),prec(F,A),relevant(S,E,T,A),not canArise(0,A),action(A).
r(S,excludes,E,T,omit(D,X)):-r(S,excludes,E,T,act(D,X)). 

% ---------- Section 4: SCENARIO-BASED CAUSALITY 

% ------------ 4.1 A Tree of Simulations

sim(S2):-emanates(S1,S2,T).
emanates(0,T,T):-occurs(0,I,T),volition(I).
emanates(S2,S2*10+T2,T2):-emanates(S1,S2,T1),occurs(S2,I,T2),T1<T2,simIndex(S2),volition(I).
simIndex(1..99).
performs(S2,A,T1):-emanates(S1,S2,T2),performs(S1,A,T1),complete(S2,A,T1),T1!=T2.
performs(S2,act(D,X),T):-occurs(S1,omit(D,X),T),emanates(S1,S2,T).

% ------------ 4.2 Simple Counter-Factual validity 

notValid(0,R,I,T,E):-r(0,R,I,T,E),emanates(0,S,T),canArise(S,E),volition(I),event(E),posRel(R). 
notValid(0,R,I,T,E):-r(0,R,I,T,E),emanates(0,S,T),not canArise(S,E),volition(I),event(E),negRel(R).
valid(0,R,I,T,E):-r(0,R,I,T,E),not notValid(0,R,I,T,E),volition(I),event(E).

% ------------ 4.3 Cruciality 

differentHistory(T2,S1,S2):-occurs(S1,I,T1),not occurs(S2,I,T1),sim(S2),volition(I),time(T2),T1<T2.
differentHistory(T,S2,S1):-differentHistory(T,S1,S2).
laterSim(exc,act(D,X),S):-occurs(0,act(D,X),T),occurs(S,omit(D,X),T),not differentHistory(T,0,S).
laterSim(exc,omit(D,X),S):-occurs(0,omit(D,X),T),occurs(S,act(D,X),T),not differentHistory(T,0,S).
laterSim(inc,I,S):-occurs(0,I,T),occurs(S,I,T),not differentHistory(T,0,S),volition(I).

notCrucial(0,R,I,T,E):-r(0,R,I,T,E),laterSim(exc,I,S),canArise(S,E),volition(I),event(E),posRel(R).
notCrucial(0,R,I,T,E):-r(0,R,I,T,E),laterSim(exc,I,S),not canArise(S,E),volition(I),event(E),negRel(R).
crucial(0,R,I,T,E):-r(0,R,I,T,E),not notCrucial(0,R,I,T,E),volition(I),event(E).

% ------------ 4.4 Necessity 

condition(inc;exc).
notNecessary(0,R,K,I,T,E):-r(0,R,I,T,E),laterSim(K,I,S),not canArise(S,E),volition(I),event(E),posRel(R).
notNecessary(0,R,K,I,T,E):-r(0,R,I,T,E),laterSim(K,I,S),canArise(S,E),volition(I),event(E),negRel(R).
necessary(0,R,K,I,T,E):-r(0,R,I,T,E),not notNecessary(0,R,K,I,T,E),volition(I),event(E),condition(K).

#hide.

#show r/5.
#show occurs/3.
#show notValid/5.
#show valid/5.
#show notCrucial/5.
#show crucial/5.
#show notNecessary/6.
#show necessary/6.
#show sim/1.
#show emanates/2.
#show complete/3.
#show holds/3.
#show good/1.
#show canArise/2.

