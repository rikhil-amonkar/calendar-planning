from z3 import *

def main():
    friends = [0, 1, 2, 3]  # 0: Jeffrey, 1: Steven, 2: Barbara, 3: John
    name_map = {
        0: "Jeffrey",
        1: "Steven",
        2: "Barbara",
        3: "John"
    }
    
    # Availability in minutes from 9:00 AM (9:00 AM = 0 minutes)
    availability = {
        0: (-60, 60),    # Jeffrey: 8:00 AM to 10:00 AM
        1: (270, 780),   # Steven: 1:30 PM to 10:00 PM
        2: (540, 750),   # Barbara: 6:00 PM to 9:30 PM
        3: (0, 270)      # John: 9:00 AM to 1:30 PM
    }
    
    # Travel times from start (Nob Hill, represented as -1) and between friends
    travel_time = {
        (-1, 0): 17,  # Nob Hill to Presidio (Jeffrey)
        (-1, 1): 8,   # Nob Hill to North Beach (Steven)
        (-1, 2): 11,  # Nob Hill to Fisherman's Wharf (Barbara)
        (-1, 3): 8,   # Nob Hill to Pacific Heights (John)
        (0, 1): 18,   # Presidio to North Beach
        (0, 2): 19,   # Presidio to Fisherman's Wharf
        (0, 3): 11,   # Presidio to Pacific Heights
        (1, 0): 17,   # North Beach to Presidio
        (1, 2): 5,    # North Beach to Fisherman's Wharf
        (1, 3): 8,    # North Beach to Pacific Heights
        (2, 0): 17,   # Fisherman's Wharf to Presidio
        (2, 1): 6,    # Fisherman's Wharf to North Beach
        (2, 3): 12,   # Fisherman's Wharf to Pacific Heights
        (3, 0): 11,   # Pacific Heights to Presidio
        (3, 1): 9,    # Pacific Heights to North Beach
        (3, 2): 13    # Pacific Heights to Fisherman's Wharf
    }
    
    n = len(friends)
    solver = Optimize()
    
    met = [Bool(f'met_{i}') for i in range(n)]
    s = [Int(f's_{i}') for i in range(n)]  # start time in minutes from 9:00 AM
    d = [Int(f'd_{i}') for i in range(n)]  # duration in minutes
    e = [s[i] + d[i] for i in range(n)]    # end time in minutes from 9:00 AM
    
    for i in range(n):
        solver.add(e[i] == s[i] + d[i])
    
    b_start = [Bool(f'b_start_{i}') for i in range(n)]
    b = [[Bool(f'b_{i}_{j}') for j in range(n)] for i in range(n)]
    
    # Constraints for meetings
    for i in range(n):
        solver.add(If(met[i], 
                      And(s[i] >= availability[i][0], 
                          e[i] <= availability[i][1], 
                          d[i] >= 1),
                      And(d[i] == 0, s[i] == 0)))
        
        solver.add(If(And(met[i], b_start[i]), 
                      s[i] >= travel_time[(-1, i)], 
                      True))
        
        for j in range(n):
            if i != j:
                solver.add(If(And(met[i], met[j], b[i][j]), 
                              s[j] >= e[i] + travel_time[(i, j)], 
                              True))
    
    # Chain constraints
    for i in range(n):
        incoming = [b_start[i]] + [b[j][i] for j in range(n) if j != i]
        solver.add(If(met[i], 
                      Or(incoming),
                      And([Not(x) for x in incoming])))
    
    solver.add(AtMost(*b_start, 1))
    
    for i in range(n):
        outgoing = [b[i][j] for j in range(n) if j != i]
        solver.add(AtMost(*outgoing, 1))
        for j in range(n):
            if i != j:
                solver.add(If(b[i][j], And(met[i], met[j])))
                solver.add(If(b[i][j], Not(b_start[i])))
                solver.add(If(b[i][j], Not(b_start[j])))
    
    edges = []
    for i in range(n):
        edges.append(b_start[i])
        for j in range(n):
            if i != j:
                edges.append(b[i][j])
    
    solver.add(Sum([If(edge, 1, 0) for edge in edges]) == Sum([If(m, 1, 0) for m in met]))
    
    # Maximize the number of friends met
    num_met = Sum([If(m, 1, 0) for m in met])
    solver.maximize(num_met)
    
    if solver.check() == sat:
        model = solver.model()
        met_friends = []
        for i in range(n):
            if is_true(model[met[i]]):
                met_friends.append(i)
        
        first = None
        for i in range(n):
            if model[b_start[i]] is not None and is_true(model[b_start[i]]):
                first = i
                break
        
        order = []
        if first is not None:
            order.append(first)
            current = first
            found_next = True
            while found_next:
                found_next = False
                for j in range(n):
                    if j != current and model[b[current][j]] is not None and is_true(model[b[current][j]]):
                        order.append(j)
                        current = j
                        found_next = True
                        break
        
        itinerary = []
        base_minutes = 9 * 60  # 9:00 AM in minutes from midnight
        for idx in order:
            start_val = model[s[idx]]
            if start_val is None:
                continue
            start_min = start_val.as_long()
            dur_min = model[d[idx]].as_long()
            total_min_start = base_minutes + start_min
            total_min_end = base_minutes + start_min + dur_min
            
            hours_start = total_min_start // 60
            minutes_start = total_min_start % 60
            hours_end = total_min_end // 60
            minutes_end = total_min_end % 60
            
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": name_map[idx],
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()