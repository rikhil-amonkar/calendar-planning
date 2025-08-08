import os
import sys
import json

def main():
    # Save original standard streams
    orig_stdout = sys.stdout
    orig_stderr = sys.stderr
    
    try:
        # Redirect stdout/stderr to avoid initialization errors
        sys.stdout = open(os.devnull, 'w')
        sys.stderr = open(os.devnull, 'w')
        
        # Import Z3 after redirection
        from z3 import Solver, Int, Bool, If, And, Or, Sum, sat
        
        # Restore streams for potential Z3 internal errors
        sys.stdout = orig_stdout
        sys.stderr = orig_stderr
        
        # Define city mapping
        city_names = {0: 'Madrid', 1: 'Dublin', 2: 'Tallinn'}
        solver = Solver()
        
        # Create variables for 7 days
        s = [Int(f's_{i}') for i in range(1, 8)]
        t = [Bool(f't_{i}') for i in range(1, 7)]
        
        # City domain constraints
        for i in range(7):
            solver.add(s[i] >= 0, s[i] <= 2)
        
        # Tallinn workshop on days 6-7
        solver.add(s[6] == 2)  # Day 7 must start in Tallinn
        
        # Travel constraints
        for i in range(6):
            direct_flight = Or(
                And(s[i] == 0, s[i+1] == 1),  # Madrid-Dublin
                And(s[i] == 1, s[i+1] == 0),
                And(s[i] == 1, s[i+1] == 2),  # Dublin-Tallinn
                And(s[i] == 2, s[i+1] == 1)
            )
            solver.add(If(t[i], direct_flight, s[i] == s[i+1]))
        
        # Count city appearances
        madrid_days = []
        dublin_days = []
        tallinn_days = []
        
        for i in range(7):
            # Starting city counts
            madrid_days.append(If(s[i] == 0, 1, 0))
            dublin_days.append(If(s[i] == 1, 1, 0))
            tallinn_days.append(If(s[i] == 2, 1, 0))
            
            # Arrival city counts for travel days
            if i < 6:
                madrid_days.append(If(And(t[i], s[i+1] == 0), 1, 0))
                dublin_days.append(If(And(t[i], s[i+1] == 1), 1, 0))
                tallinn_days.append(If(And(t[i], s[i+1] == 2), 1, 0))
        
        # Add city total constraints
        solver.add(Sum(madrid_days) == 4)
        solver.add(Sum(dublin_days) == 3)
        solver.add(Sum(tallinn_days) == 2)
        
        # Exactly 2 travel days
        solver.add(Sum([If(t_i, 1, 0) for t_i in t]) == 2)
        
        # Solve and capture results
        result = {}
        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            s_vals = [model.evaluate(s_i).as_long() for s_i in s]
            t_vals = [model.evaluate(t_i) for t_i in t]
            
            for day in range(1, 8):
                idx = day - 1
                itinerary.append({'day': day, 'city': city_names[s_vals[idx]]})
                if day < 7 and t_vals[idx]:
                    itinerary.append({'day': day, 'city': city_names[s_vals[idx+1]]})
            result = {'itinerary': itinerary}
        else:
            result = {'error': 'No solution found'}
        
        # Output final result
        print(json.dumps(result))
        
    except Exception as e:
        # Restore streams before reporting errors
        sys.stdout = orig_stdout
        sys.stderr = orig_stderr
        print(json.dumps({'error': f'Execution failed: {str(e)}'}))

if __name__ == '__main__':
    main()