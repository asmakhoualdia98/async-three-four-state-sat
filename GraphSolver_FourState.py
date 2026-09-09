# GraphSolver_FourState.py

import sys
import os
from GraphModel_FourState import GraphModel


VALID_BEHAVIORS = {"CONV", "DIV"}
VALID_DAEMONS = {"SYNC", "CEN","LOC","DIS-UNFAIR"}

def check_args(num_nodes, behavior, daemon):
    errors = []

    if behavior not in VALID_BEHAVIORS:
        errors.append(f"❌ Invalid behavior: '{behavior}'. Choose 'CONV' or 'DIV'.")

    if daemon not in VALID_DAEMONS:
        errors.append(f"❌ Invalid configuration daemon: '{daemon}'. Choose among {', '.join(VALID_DAEMONS)}.")
    
    return errors

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("❗ Usage: python GraphSolver.py <num_nodes> <mode> <daemon>")
        sys.exit(1)

    
    try:
        num_nodes = int(sys.argv[1])
        
    except ValueError:
        print("❗ 'num_nodes' must be integers.")
        sys.exit(1)

    behavior = sys.argv[2].upper()
    daemon = sys.argv[3].upper()

    errors = check_args(num_nodes, behavior, daemon)
    if errors:
        for error in errors:
            print(error)
        sys.exit(1)

    # Build the output path
    output_dir = os.path.join("Benchmark", "Four State", behavior, daemon)
    os.makedirs(output_dir, exist_ok=True)

    output_path = os.path.join(output_dir, f"{num_nodes}_{behavior}_{daemon}.cnf")

    try:
        model_instance = GraphModel(num_nodes, behavior, daemon)
        model_instance.generate_cnf(output_path)  # call with single argument, output_path
        print(f"✅ CNF file generated: {output_path}")
    except Exception as e:
        print(f"❌ Error during model generation: {e}")
        sys.exit(1)
