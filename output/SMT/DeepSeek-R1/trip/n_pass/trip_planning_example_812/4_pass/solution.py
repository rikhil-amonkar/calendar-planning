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
    
    # Calculate pass sequence start and end
    pass_start = starts[sequence_clean[0]]
    pass_days = sum(req_days_dict[loc] for loc in sequence_clean)
    pass_end = pass_start + pass_days - 1
    
    # Separate non-pass locations
    non_pass = all_locations - set(sequence_clean)
    is_before = {}
    for loc in non_pass:
        is_before[loc] = Bool(f'before_{loc}')
        # Constrain non-pass locations to be entirely before or after pass sequence
        s.add(Or(
            And(is_before[loc], starts[loc] + req_days_dict[loc] <= pass_start),
            And(Not(is_before[loc]), starts[loc] >= pass_end + 1)
        ))
    
    # Non-overlap constraints for non-pass locations in the same segment
    non_pass_list = list(non_pass)
    for i in range(len(non_pass_list)):
        for j in range(i + 1, len(non_pass_list)):
            loc1 = non_pass_list[i]
            loc2 = non_pass_list[j]
            # If both are before, enforce non-overlap
            s.add(If(And(is_before[loc1], is_before[loc2]),
                     Or(starts[loc1] + req_days_dict[loc1] <= starts[loc2],
                        starts[loc2] + req_days_dict[loc2] <= starts[loc1]),
                     True))
            # If both are after, enforce non-overlap
            s.add(If(And(Not(is_before[loc1]), Not(is_before[loc2])),
                     Or(starts[loc1] + req_days_dict[loc1] <= starts[loc2],
                        starts[loc2] + req_days_dict[loc2] <= starts[loc1]),
                     True))
    
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