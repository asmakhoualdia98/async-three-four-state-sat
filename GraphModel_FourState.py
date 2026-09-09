import os
import math
from pysat.formula import CNF
from pysat.card import CardEnc, EncType

class GraphModel:
    def __init__(self, num_nodes, mode, daemon):
    
        self.graph_type = "ring"

        self.num_nodes = num_nodes
        
        self.modulus = 2
        
        # Execution mode (CONV, DIV)
        self.mode = mode.upper()
        
        # Daemon
        self.daemon = daemon.upper()
        
        # Number of allowed configurations
        self.max_steps = 20 * self.num_nodes


    # --------------------------------------------------
    # Variables
    # --------------------------------------------------

    def stx(self, i, t):
        return i * self.max_steps + t + 1
        
    def stup(self, i, t):
        base = self.stx(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1

    def autsuc(self, i, t):
        base = self.stup(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autsucone(self, i, t):
        base = self.autsuc(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autsuctwo(self, i, t):
        base = self.autsucone(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autpred(self, i, t):
        base = self.autsuctwo(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autpredone(self, i, t):
        base = self.autpred(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autpredtwo(self, i, t):
        base = self.autpredone(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
        
    def actsuc(self, i, t):
        base = self.autpredtwo(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
        
    def actpred(self, i, t):
        base = self.actsuc(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1

    def aut(self, i, t):
        base = self.actpred(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1

    def act(self, i, t):
        base = self.aut(self.num_nodes - 1, self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
    def cyc(self, t):
        base = self.act(self.num_nodes - 1, self.max_steps - 1)
        return base + t + 1
        
        
    def simx(self, i, t):
        base = self.cyc( self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
        
    def simup(self, i, t):
        base = self.simx(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
    def simonex(self, i, t):
        base = self.simup(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
        
    def simoneup(self, i, t):
        base = self.simonex(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
        
    def simtwox(self, i, t):
        base = self.simoneup(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
        
    def simtwoup(self, i, t):
        base = self.simtwox(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        

    # --------------------------------------------------
    # Predecessor Authorization constraints
    # --------------------------------------------------

    def add_aut_pred_suc_clauses(self, cnf):
        n = self.num_nodes
        t_max = self.max_steps
    
        for t in range(t_max):
        
            # Setting the up cst values for 0 and n-1
        
            cnf.append(
                [self.stup(0, t)]
            )
            
            cnf.append(
                [-self.stup(n-1, t)]
            )
        
           
            for p in range(n-1):
                suc = (p + 1) % n
                
                ######## Successor
                
                # First Direction of the equivalence ->
                
                cnf.append(
                    [-self.autsuc(p, t)] +
                    [self.autsucone(p, t)]
                )
                
                cnf.append(
                    [-self.autsuc(p, t)] +
                    [self.autsuctwo(p, t)]
                )
                
                cnf.append(
                    [-self.autsuc(p, t)] +
                    [self.stup(p, t)]
                )
                
                cnf.append(
                    [-self.autsuc(p, t)] +
                    [-self.stup(suc, t)]
                )
                
                # Opposite Direction of the equivalence <-
                
                cnf.append(
                    [self.autsuc(p, t)] +
                    [-self.autsucone(p, t)] +
                    [-self.autsuctwo(p, t)] +
                    [-self.stup(p, t)] +
                    [self.stup(suc, t)]
                )
                
                # intermediate variables
                
                # 1
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [self.stx(suc, t)] +
                    [-self.autsucone(p, t)]
                )
                
                cnf.append(
                    [self.stx(p, t)] +
                    [self.autsucone(p, t)]
                )
                
                cnf.append(
                    [-self.stx(suc, t)] +
                    [self.autsucone(p, t)]
                )
                
                # 2 
                
                cnf.append(
                    [self.stx(p, t)] +
                    [-self.stx(suc, t)] +
                    [-self.autsuctwo(p, t)]
                )
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [self.autsuctwo(p, t)]
                )
                
                cnf.append(
                    [self.stx(suc, t)] +
                    [self.autsuctwo(p, t)]
                )
                
            for p in range(1, n):
                pred = (p - 1) % n   
                ######## Predecessor
                
                # First Direction of the equivalence ->
                
                cnf.append(
                    [self.autpred(p, t)] +
                    [self.autpredone(p, t)]
                )
                
                cnf.append(
                    [self.autpred(p, t)] +
                    [self.autpredtwo(p, t)]
                )
                
                
                
                # Opposite Direction of the equivalence <-
                
                cnf.append(
                    [-self.autpred(p, t)] +
                    [-self.autpredone(p, t)] +
                    [-self.autpredtwo(p, t)]
                )
                
                # intermediate variables
                
                # 1
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [self.stx(pred, t)] +
                    [-self.autpredone(p, t)]
                )
                
                cnf.append(
                    [self.stx(p, t)] +
                    [self.autpredone(p, t)]
                )
                
                cnf.append(
                    [-self.stx(pred, t)] +
                    [self.autpredone(p, t)]
                )
                
                # 2 
                
                cnf.append(
                    [self.stx(p, t)] +
                    [-self.stx(pred, t)] +
                    [-self.autpredtwo(p, t)]
                )
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [self.autpredtwo(p, t)]
                )
                
                cnf.append(
                    [self.stx(pred, t)] +
                    [self.autpredtwo(p, t)]
                )   
        
                
        for t in range(t_max):
            # Token implication to enabling
            
            
            
            cnf.append(
                [-self.aut(n-1, t)] +
                [self.autpred(n-1, t)]
            )
            
            cnf.append(
                [self.aut(n-1, t)] +
                [-self.autpred(n-1, t)]
            )
            
            
            
            
            cnf.append(
                [-self.aut(0, t)] +
                [self.autsuc(0, t)]
            )
            
            cnf.append(
                [self.aut(0, t)] +
                [-self.autsuc(0, t)]
            )
       
       
        for p in range(1, n-1):
        
            for t in range(t_max):
            
                # Token implication to enabling
                
                
                
                cnf.append(
                    [-self.aut(p, t)] +
                    [self.autpred(p, t)] +
                    [self.autsuc(p, t)]
                )
                
                
                
                
                cnf.append(
                    [self.aut(p, t)] +
                    [-self.autpred(p, t)]
                )
                
                cnf.append(
                    [self.aut(p, t)] +
                    [-self.autsuc(p, t)]
                )
    
                
    # --------------------------------------------------
    # Process Activation constraints
    # --------------------------------------------------

                
    def add_act_pred_suc_clauses(self, cnf):
    
        n = self.num_nodes
        t_max = self.max_steps

        for t in range(t_max - 1):
        
            
            
            cnf.append([self.act(p,t) for p in range(n)])
        
            
            
            for p in range(n-1):
                cnf.append(
                    [-self.actsuc(p, t)] +
                    [self.autsuc(p, t)]
                )
                
            
               
            for p in range(1, n):
                cnf.append(
                    [-self.actpred(p, t)] +
                    [self.autpred(p, t)]
                )
                
                
                
            for p in range(1, n-1):  
                
                
            
                cnf.append(
                    [-self.actpred(p, t)] +
                    [-self.actsuc(p, t)]
                )
                
                
                
                
                
                cnf.append(
                    [-self.act(p, t)] +
                    [self.actpred(p, t)] +
                    [self.actsuc(p, t)]
                )
                
                
                
                cnf.append(
                    [self.act(p, t)] +
                    [-self.actpred(p, t)]
                )
                
                cnf.append(
                    [self.act(p, t)] +
                    [-self.actsuc(p, t)]
                )
                
            
            
            cnf.append(
                [-self.act(n-1, t)] +
                [self.actpred(n-1, t)]
            )
            
            cnf.append(
                [self.act(n-1, t)] +
                [-self.actpred(n-1, t)]
            )
            
            
            
            cnf.append(
                [-self.act(0, t)] +
                [self.actsuc(0, t)]
            )
            
            cnf.append(
                [self.act(0, t)] +
                [-self.actsuc(0, t)]
            )
                

    # --------------------------------------------------
    # Update rules
    # --------------------------------------------------
    


    def add_update_clauses(self, cnf):
        n = self.num_nodes
        t_max = self.max_steps
    
        for t in range(t_max - 1):
    
            # -------------------------
            for p in range(n):
                # Non activable → persistance    
              
                #x
                
                cnf.append([
                    self.act(p, t),
                    -self.stx(p, t),
                    self.stx(p, t + 1)
                ])
                
                cnf.append([
                    self.act(p, t),
                    self.stx(p, t),
                    -self.stx(p, t + 1)
                ])
                
                #up
                
                cnf.append([
                    self.act(p, t),
                    -self.stup(p, t),
                    self.stup(p, t + 1)
                ])
                
                cnf.append([
                    self.act(p, t),
                    self.stup(p, t),
                    -self.stup(p, t + 1)
                ])
                
            # activable → update  
            # -------------------------
            
            cnf.append(
                [-self.stx(0, t)] +
                [-self.actsuc(0, t)] +
                [-self.stx(0, t+1)]
            )
            
            cnf.append(
                [self.stx(0, t)] +
                [-self.actsuc(0, t)] +
                [self.stx(0, t+1)]
            )
            
            for p in range(1, n-1):
            
                cnf.append(
                    [-self.actsuc(p, t)] +
                    [-self.stup(p, t+1)]
                )
                
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [-self.actsuc(p, t)] +
                    [self.stx(p, t+1)]
                )
                
                cnf.append(
                    [self.stx(p, t)] +
                    [-self.actsuc(p, t)] +
                    [-self.stx(p, t+1)]
                )
                
                cnf.append(
                    [-self.actpred(p, t)] +
                    [self.stup(p, t+1)]
                )
                
            for p in range(1, n):
                
                cnf.append(
                    [-self.stx(p, t)] +
                    [-self.actpred(p, t)] +
                    [-self.stx(p, t+1)]
                )
                
                cnf.append(
                    [self.stx(p, t)] +
                    [-self.actpred(p, t)] +
                    [self.stx(p, t+1)]
                )
                
                
                
    

    

    
    def add_div_aut(self, cnf):
        n = self.num_nodes
        t_max = self.max_steps
        variables = [self.aut(i, 0) for i in range(n)]
        top_id = cnf.nv
        card = CardEnc.atleast(
            lits=variables,
            bound=2,
            encoding=EncType.cardnetwrk,
            top_id=top_id
        )
        cnf.extend(card.clauses)

    # --------------------------------------------------
    # divergence constraint
    # --------------------------------------------------
    
    def add_divergence(self, cnf):
        
        # Formule 1
        
        clause = [self.cyc(t) for t in range(1, self.max_steps)]
        cnf.append(clause)
            
        # Formule 2 :
        
        for t in range(1, self.max_steps):
            for i in range(self.num_nodes):
                clause = [self.simx(i, t), 
                          -self.cyc(t)]
                cnf.append(clause)
                
                clause = [self.simup(i, t), 
                          -self.cyc(t)]
                cnf.append(clause)
            
                clause = [-self.simx(i, t),
                          -self.simup(i, t),
                          self.cyc(t)]
                cnf.append(clause)
                
                
                # 1
                
                clause = [-self.simx(i, t),
                          self.simonex(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.simx(i, t),
                          self.simtwox(i,t)]
                cnf.append(clause)
                
                
                clause = [self.simx(i, t),
                          -self.simonex(i,t),
                          -self.simtwox(i,t)]
                cnf.append(clause)
                
                # 2
                
                clause = [-self.simup(i, t),
                          self.simoneup(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.simup(i, t),
                          self.simtwoup(i,t)]
                cnf.append(clause)
                
                
                clause = [self.simup(i, t),
                          -self.simoneup(i,t),
                          -self.simtwoup(i,t)]
                cnf.append(clause)
                
                
                # simone
                
                # x
                
                clause = [-self.stx(i, 0),
                          self.stx(i, t),
                          -self.simonex(i,t)]
                cnf.append(clause)
                
                
                clause = [self.stx(i, 0),
                          self.simonex(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.stx(i, t),
                          self.simonex(i,t)]
                cnf.append(clause)
                
                
                # up
                
                clause = [-self.stup(i, 0),
                          self.stup(i, t),
                          -self.simoneup(i,t)]
                cnf.append(clause)
                
                
                clause = [self.stup(i, 0),
                          self.simoneup(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.stup(i, t),
                          self.simoneup(i,t)]
                cnf.append(clause)
                
                
                
                
                # simtwo
                
                # x
                
                clause = [self.stx(i, 0),
                          -self.stx(i, t),
                          -self.simtwox(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.stx(i, 0),
                          self.simtwox(i,t)]
                cnf.append(clause)
                
                
                clause = [self.stx(i, t),
                          self.simtwox(i,t)]
                cnf.append(clause)
                
                # up
                
                clause = [self.stup(i, 0),
                          -self.stup(i, t),
                          -self.simtwoup(i,t)]
                cnf.append(clause)
                
                
                clause = [-self.stup(i, 0),
                          self.simtwoup(i,t)]
                cnf.append(clause)
                
                
                clause = [self.stup(i, t),
                          self.simtwoup(i,t)]
                cnf.append(clause)
    
    
    # --------------------------------------------------
    # central daemon constraint
    # --------------------------------------------------          
                
    def add_central(self, cnf):
        n = self.num_nodes
        top_id = cnf.nv
        for t in range(self.max_steps - 1):
            variables = [self.act(i, t) for i in range(n)]
            card = CardEnc.atmost(
                lits=variables,
                bound=1,
                encoding=EncType.cardnetwrk,
                top_id=top_id
            )
            top_id = card.nv
            cnf.extend(card.clauses)


    # --------------------------------------------------
    # local daemon constraint
    # --------------------------------------------------  
    
    def add_local(self, cnf):
        n = self.num_nodes
        
        t_max = self.max_steps

        for t in range(t_max - 1):
            for p in range(n):
                
                clause1 = [
                    -self.act(p,t), 
                    -self.act((p-1)%n,t)
                ]
                
                cnf.append(clause1)
                
                clause2 = [
                    -self.act(p,t), 
                    -self.act((p+1)%n,t)
                ]
                
                cnf.append(clause2)
    
    # --------------------------------------------------
    # synchronous daemon constraint
    # --------------------------------------------------             
                
    def add_sync(self, cnf):
        n = self.num_nodes
        
        t_max = self.max_steps

        for t in range(t_max - 1):
            for p in range(n):
                
                clause1 = [
                    -self.aut(p,t), 
                    self.act(p,t)
                ]
                
                cnf.append(clause1)

    # --------------------------------------------------
    # convergence constraint
    # --------------------------------------------------  

    
    def add_cnv(self, cnf):
        n = self.num_nodes
        t_max = self.max_steps
        variables = [self.aut(i, t_max - 1) for i in range(n)]
        top_id = cnf.nv
        card = CardEnc.atleast(
            lits=variables,
            bound=2,
            encoding=EncType.cardnetwrk,
            top_id=top_id
        )
        cnf.extend(card.clauses)

    # --------------------------------------------------
    # Generation
    # --------------------------------------------------

    def generate_cnf(self, output_path):
        cnf = CNF()
        
        self.add_update_clauses(cnf)
        self.add_aut_pred_suc_clauses(cnf)
        self.add_act_pred_suc_clauses(cnf)
        
        
        if self.mode == "CONV":
            self.add_cnv(cnf)

        elif self.mode == "DIV":
            self.add_div_aut(cnf)
            self.add_divergence(cnf)

            
        # --- DAEMONS ASSUPTIONS---
        
        if self.daemon == "CEN":
            self.add_central(cnf)
        
        elif self.daemon == "SYNC":
            self.add_sync(cnf)
        
        elif self.daemon == "LOC":
            self.add_local(cnf)
        
        elif self.daemon == "DIS-UNFAIR":
            pass
                

        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        cnf.to_file(output_path)
        print(f"✅ CNF file generated: {output_path}")
