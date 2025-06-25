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
    
    sequence = passes[0]['sequence']
    sequence_clean = [s.strip('"') for s in sequence]
    
    starts = {loc: Int(f'start_{loc}') for loc in all_locations}
    s = Solver()
    
    for loc in all_locations:
        s.add(starts[loc] >= 1)
        s.add(starts[loc] <= total_days - req_days_dict[loc] + 1)
    
    for loc in all_locations:
        for other in all_locations:
            if loc != other:
                s.add(Or(
                    starts[loc] + req_days_dict[loc] <= starts[other],
                    starts[other] + req_days_dict[other] <= starts[loc]
                ))
    
    for i in range(len(sequence_clean) - 1):
        loc1 = sequence_clean[i]
        loc2 = sequence_clean[i+1]
        s.add(starts[loc1] + req_days_dict[loc1] == starts[loc2])
    
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