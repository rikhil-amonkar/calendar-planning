import json
import sys
from z3 import *

def main():
    input_str = sys.stdin.read()
    data = json.loads(input_str)
    
    requests = data['requests']
    passes = data['passes']
    
    req_days_dict = {}
    all_locations = set()
    for req in requests:
        place_clean = req['place'].strip('"')
        req_days_dict[place_clean] = req['days']
        all_locations.add(place_clean)
    
    total_days = sum(req_days_dict.values())
    total_max = 1000  # Arbitrary upper bound to prevent unbounded variables
    
    sequence = passes[0]['sequence']
    sequence_clean = [s.strip('"') for s in sequence]
    
    starts = {loc: Int(f'start_{loc}') for loc in all_locations}
    s = Solver()
    
    # Set bounds for each location's start day
    for loc in all_locations:
        s.add(starts[loc] >= 1)
        s.add(starts[loc] <= total_max - req_days_dict[loc] + 1)
    
    # Ensure the pass sequence is contiguous
    for i in range(len(sequence_clean) - 1):
        loc1 = sequence_clean[i]
        loc2 = sequence_clean[i+1]
        s.add(starts[loc2] == starts[loc1] + req_days_dict[loc1])
    
    # Calculate total days in the pass sequence
    pass_days = sum(req_days_dict[loc] for loc in sequence_clean)
    pass_start = starts[sequence_clean[0]]
    
    # Separate non-pass locations
    non_pass = all_locations - set(sequence_clean)
    if non_pass:
        # Constrain non-pass locations to be before or after the pass sequence
        for loc in non_pass:
            s.add(Or(
                starts[loc] + req_days_dict[loc] <= pass_start,  # Before
                starts[loc] >= pass_start + pass_days             # After
            ))
        
        # Apply non-overlap constraints only within the same group (before or after)
        non_pass_list = list(non_pass)
        for i in range(len(non_pass_list)):
            for j in range(i+1, len(non_pass_list)):
                loc1 = non_pass_list[i]
                loc2 = non_pass_list[j]
                s.add(If(
                    Or(
                        And(starts[loc1] + req_days_dict[loc1] <= pass_start, 
                            starts[loc2] + req_days_dict[loc2] <= pass_start),
                        And(starts[loc1] >= pass_start + pass_days, 
                            starts[loc2] >= pass_start + pass_days)
                    ),
                    Or(
                        starts[loc1] + req_days_dict[loc1] <= starts[loc2],
                        starts[loc2] + req_days_dict[loc2] <= starts[loc1]
                    ),
                    True  # No constraint if in different groups
                ))
    
    # Check for a solution and output
    if s.check() == sat:
        model = s.model()
        result = []
        for loc in all_locations:
            start_val = model[starts[loc]].as_long()
            end_val = start_val + req_days_dict[loc] - 1
            result.append((loc, start_val, end_val))
        result.sort(key=lambda x: x[1])
        for loc, start, end in result:
            print(f"{loc} {start} {end}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()