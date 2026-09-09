import os
import math
from pysat.formula import CNF
from pysat.card import CardEnc, EncType

class GraphModel:
    def __init__(self, num_nodes, mode, daemon):
    
        self.graph_type = "ring"

        self.num_nodes = num_nodes
        
        self.modulus = 3
        
        # Execution mode (CONV, DIV)
        self.mode = mode.upper()
        
        # Daemon
        self.daemon = daemon.upper()
        
        # Number of allowed configurations
        self.max_steps = 20 * self.num_nodes


    # --------------------------------------------------
    # Variables
    # --------------------------------------------------

    def st(self, i, t, v):
        return i * self.max_steps * self.modulus + t * self.modulus + v + 1

    def autsuc(self, i, t):
        base = self.st(self.num_nodes - 1,
                        self.max_steps - 1,
                        self.modulus - 1)
        return base + i * self.max_steps + t  + 1
        
    def autpred(self, i, t):
        base = self.autsuc(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps + t  + 1
        
    def autpredv(self, i, t, v):
        base = self.autpred(self.num_nodes - 1,
                        self.max_steps - 1)
        return base + i * self.max_steps * self.modulus + t * self.modulus + v + 1
        
        
    def autsucv(self, i, t, v):
        base = self.autpredv(self.num_nodes - 1,
                        self.max_steps - 1,
                        self.modulus - 1)
        return base + i * self.max_steps * self.modulus + t * self.modulus + v + 1
        

    def aut(self, i, t):
        base = self.autsucv(self.num_nodes - 1,
                        self.max_steps - 1,
                        self.modulus - 1)
        return base + i * self.max_steps + t + 1

    def act(self, i, t):
        base = self.aut(self.num_nodes - 1, self.max_steps - 1)
        return base + i * self.max_steps + t + 1
        
    
    def cyc(self, t):
        
        return self.act(self.num_nodes - 1, self.max_steps - 1) + t + 1

    def sim(self, i, t, value):
        return self.cyc(self.max_steps - 1) + i * self.max_steps * self.modulus + t * self.modulus + value + 1

    

    # --------------------------------------------------
    # Clock uniqueness
    # --------------------------------------------------

    def add_uniqueness_clauses(self, cnf):
        top_id = self.sim(self.num_nodes - 1, self.max_steps - 1, self.modulus - 1)
        for t in range(self.max_steps):
            for i in range(self.num_nodes):
                variables = [self.st(i, t, v) for v in range(self.modulus)]
                card = CardEnc.equals(
                    lits=variables,
                    bound=1,
                    encoding=EncType.cardnetwrk,
                    top_id=top_id
                )
                top_id = card.nv
                cnf.extend(card.clauses)
                
                
    
    #---------------------------------------------------
    # Authorization constraints
    #---------------------------------------------------
    
    def add_aut_pred_suc_clauses(self, cnf):
        n = self.num_nodes
        m = self.modulus
        t_max = self.max_steps
    
        for t in range(t_max ):
        
            ########Successor
            for p in range(n-1):
                
                suc = (p + 1) % n
                
                
                
                cnf.append(
                    [-self.autsuc(p, t)] +
                    [self.autsucv(p, t, v) for v in range(m)]
                )
                
                
                
                for v in range(m):
                    cnf.append(
                        [self.autsuc(p, t)] +
                        [-self.autsucv(p, t, v)]
                    )
                    
                     
                    
                    cnf.append(
                        [self.autsucv(p, t, v)] +
                        [-self.st(p, t, v )]+
                        [-self.st(suc, t, (v+1) % m)]
                    )
                    
                    
                    
                    cnf.append(
                        [-self.autsucv(p, t, v)] +
                        [self.st(suc, t, (v+1) % m)]
                    )
                    
                    
                    cnf.append(
                        [-self.autsucv(p, t, v)] +
                        [self.st(p, t, v )]
                    )
                    
                
            ########Predecessor
                 
            for p in range(1, n):  
            
                pred = (p - 1) % n
                
                
                
                cnf.append(
                    [-self.autpred(p, t)] +
                    [self.autpredv(p, t, v) for v in range(m)]
                )
                
                
            
                for v in range(m):
                    cnf.append(
                        [self.autpred(p, t)] +
                        [-self.autpredv(p, t, v)]
                    )
                    
            for p in range(1, n-1): 
                pred = (p - 1) % n
                
                for v in range(m):
                
                    
                
                    cnf.append(
                        [self.autpredv(p, t, v)] +
                        [-self.st(p, t, v )]+
                        [-self.st(pred, t, (v+1) % m)]
                    )
                    
                    
                    
                    
                    
                    cnf.append(
                        [-self.autpredv(p, t, v)] +
                        [self.st(pred, t, (v+1) % m)]
                    )
                    
                    
                    cnf.append(
                        [-self.autpredv(p, t, v)] +
                        [self.st(p, t, v )]
                    )
            
            
            
            for v in range(m):
            
                cnf.append(
                    [-self.autpredv(n-1, t, v)] +
                    [self.st(0, t, v )]
                )
                
                cnf.append(
                    [-self.autpredv(n-1, t, v)] +
                    [self.st(n-2, t, v )]
                )
                
                cnf.append(
                    [-self.autpredv(n-1, t, v)] +
                    [-self.st(n-1, t, (v+1) % m)]
                )
                
                
            
            
                cnf.append(
                    [self.autpredv(n-1, t, v)] +
                    [-self.st(0, t, v )]+
                    [-self.st(n-2, t, v )]+
                    [self.st(n-1, t, (v+1) % m)]
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
        m = self.modulus
        t_max = self.max_steps

        for t in range(t_max - 1):
        
            
            
            cnf.append([self.act(p,t) for p in range(n)])
        
            
            
            for p in range(n):
                cnf.append(
                    [-self.act(p, t)] +
                    [self.aut(p, t)]
                )
                
            
    # --------------------------------------------------
    # Update rules
    # --------------------------------------------------
    
    def add_update_test_clauses(self, cnf):
        n = self.num_nodes
        m = self.modulus
        t_max = self.max_steps
    
        for t in range(t_max - 1):
    
            for p in range(n):
                for v in range(m):
                    
                    
                    cnf.append([
                        -self.st(p, t, v),
                        self.act(p, t),
                        self.st(p, t + 1, v)
                    ])
    
            # -------------------------
            # p ≠ 0 and n-1
            # -------------------------
            for p in range(1, n-1):
                
    
                for v in range(m):
                    # Activated
                    
                    
                
                    cnf.append([
                        -self.st(p, t, v),
                        -self.act(p, t),
                        self.st(p, t + 1, (v+1) % m)
                    ])
                    
                    

            # -------------------------
            # p = n-1
            # -------------------------
            
            
            
            for v in range(m):
    
                # Activated
                cnf.append([
                    -self.act(n-1, t),
                    -self.st(n-2, t, v),
                    self.st(n-1, t + 1, (v + 1) % m)
                ])

            # -------------------------
            # p = 0
            # -------------------------
            
            
            
            for v in range(m):
    
                # Activated
                cnf.append([
                    -self.act(0, t),
                    -self.st(0, t, v),
                    self.st(0, t + 1, (v + 2) % m)
                ])

    
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
    # divergence constraints
    # --------------------------------------------------
    

    
    def add_div_aut(self, cnf):
        n = self.num_nodes
        variables = [self.aut(i, 0) for i in range(n)]
        top_id = cnf.nv
        card = CardEnc.atleast(
            lits=variables,
            bound=2,
            encoding=EncType.cardnetwrk,
            top_id=top_id
        )
        cnf.extend(card.clauses)

    
    def add_divergence(self, cnf):
        
        # Formule 1
        
        clause = [self.cyc(t) for t in range(1, self.max_steps)]
        cnf.append(clause)
            
        # Formule 2 :
        
        for t in range(1, self.max_steps):
            for i in range(self.num_nodes):
                clause = [self.sim(i, t, v) for v in range(self.modulus)] + [-self.cyc(t)]
                cnf.append(clause)
     
        
        # Formule 3 :
        for t in range(1, self.max_steps):
            for i in range(self.num_nodes):
                for v in range(self.modulus):
                
                    clause1 = [
                        self.st(i, 0, v), 
                        -self.sim(i,t, v)
                    ]
                    
                    cnf.append(clause1)
                    
                    clause2 = [
                        self.st(i, t, v), 
                        -self.sim(i,t, v)
                    ]
                    
                    cnf.append(clause2)
                    
                    
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
    # Generation
    # --------------------------------------------------

    def generate_cnf(self, output_path):
        cnf = CNF()
        
        self.add_uniqueness_clauses(cnf)
        self.add_aut_pred_suc_clauses(cnf)
        self.add_act_pred_suc_clauses(cnf)
        self.add_update_test_clauses(cnf)
        
        
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
