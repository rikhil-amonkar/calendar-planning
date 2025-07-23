import json
from z3 import *

def main():
    # Parse travel times
    travel_text = """
    Marina District to Richmond District: 11.
    Marina District to Union Square: 16.
    Marina District to Nob Hill: 12.
    Marina District to Fisherman's Wharf: 10.
    Marina District to Golden Gate Park: 18.
    Marina District to Embarcadero: 14.
    Marina District to Financial District: 17.
    Marina District to North Beach: 11.
    Marina District to Presidio: 10.
    Richmond District to Marina District: 9.
    Richmond District to Union Square: 21.
    Richmond District to Nob Hill: 17.
    Richmond District to Fisherman's Wharf: 18.
    Richmond District to Golden Gate Park: 9.
    Richmond District to Embarcadero: 19.
    Richmond District to Financial District: 22.
    Richmond District to North Beach: 17.
    Richmond District to Presidio: 7.
    Union Square to Marina District: 18.
    Union Square to Richmond District: 20.
    Union Square to Nob Hill: 9.
    Union Square to Fisherman's Wharf: 15.
    Union Square to Golden Gate Park: 22.
    Union Square to Embarcadero: 11.
    Union Square to Financial District: 9.
    Union Square to North Beach: 10.
    Union Square to Presidio: 24.
    Nob Hill to Marina District: 11.
    Nob Hill to Richmond District: 14.
    Nob Hill to Union Square: 7.
    Nob Hill to Fisherman's Wharf: 10.
    Nob Hill to Golden Gate Park: 17.
    Nob Hill to Embarcadero: 9.
    Nob Hill to Financial District: 9.
    Nob Hill to North Beach: 8.
    Nob Hill to Presidio: 17.
    Fisherman's Wharf to Marina District: 9.
    Fisherman's Wharf to Richmond District: 18.
    Fisherman's Wharf to Union Square: 13.
    Fisherman's Wharf to Nob Hill: 11.
    Fisherman's Wharf to Golden Gate Park: 25.
    Fisherman's Wharf to Embarcadero: 8.
    Fisherman's Wharf to Financial District: 11.
    Fisherman's Wharf to North Beach: 6.
    Fisherman's Wharf to Presidio: 17.
    Golden Gate Park to Marina District: 16.
    Golden Gate Park to Richmond District: 7.
    Golden Gate Park to Union Square: 22.
    Golden Gate Park to Nob Hill: 20.
    Golden Gate Park to Fisherman's Wharf: 24.
    Golden Gate Park to Embarcadero: 25.
    Golden Gate Park to Financial District: 26.
    Golden Gate Park to North Beach: 23.
    Golden Gate Park to Presidio: 11.
    Embarcadero to Marina District: 12.
    Embarcadero to Richmond District: 21.
    Embarcadero to Union Square: 10.
    Embarcadero to Nob Hill: 10.
    Embarcadero to Fisherman's Wharf: 6.
    Embarcadero to Golden Gate Park: 25.
    Embarcadero to Financial District: 5.
    Embarcadero to North Beach: 5.
    Embarcadero to Presidio: 20.
    Financial District to Marina District: 15.
    Financial District to Richmond District: 21.
    Financial District to Union Square: 9.
    Financial District to Nob Hill: 8.
    Financial District to Fisherman's Wharf: 10.
    Financial District to Golden Gate Park: 23.
    Financial District to Embarcadero: 4.
    Financial District to North Beach: 7.
    Financial District to Presidio: 22.
    North Beach to Marina District: 9.
    North Beach to Richmond District: 18.
    North Beach to Union Square: 7.
    North Beach to Nob Hill: 7.
    North Beach to Fisherman's Wharf: 5.
    North Beach to Golden Gate Park: 22.
    North Beach to Embarcadero: 6.
    North Beach to Financial District: 8.
    North Beach to Presidio: 17.
    Presidio to Marina District: 11.
    Presidio to Richmond District: 7.
    Presidio to Union Square: 22.
    Presidio to Nob Hill: 18.
    Presidio to Fisherman's Wharf: 19.
    Presidio to Golden Gate Park: 12.
    Presidio to Embarcadero: 20.
    Presidio to Financial District: 23.
    Presidio to North Beach: 18.
    """
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.endswith('.'):
            line = line[:-1]
        parts = line.split(':')
        if len(parts) < 2:
            continue
        from_to_str = parts[0].strip()
        time_str = parts[1].strip()
        try:
            time_val = int(time_str)
        except:
            continue
        if " to " in from_to_str:
            locs = from_to_str.split(" to ")
            from_loc = locs[0].strip()
            to_loc = locs[1].strip()
            if from_loc not in travel_dict:
                travel_dict[from_loc] = {}
            travel_dict[from_loc][to_loc] = time_val

    meetings = [
        (0, "Dummy", "Marina District", 0, 0, 0),
        (1, "Stephanie", "Richmond District", 435, 750, 75),
        (2, "William", "Union Square", 105, 510, 45),
        (3, "Elizabeth", "Nob Hill", 195, 360, 105),
        (4, "Joseph", "Fisherman's Wharf", 225, 300, 75),
        (5, "Anthony", "Golden Gate Park", 240, 690, 75),
        (6, "Barbara", "Embarcadero", 615, 690, 75),
        (7, "Carol", "Financial District", 165, 435, 60),
        (8, "Sandra", "North Beach", 60, 210, 15),
        (9, "Kenneth", "Presidio", 735, 795, 45)
    ]

    s = Solver()

    chosen_all = []
    for i in range(10):
        if i == 0:
            chosen_all.append(True)
        else:
            chosen_all.append(Bool(f"chosen_{i}"))
    
    start = [Int(f"start_{i}") for i in range(10)]
    end = [Int(f"end_{i}") for i in range(10)]
    
    x = [[None]*10 for _ in range(10)]
    for i in range(10):
        for j in range(10):
            if i == j:
                continue
            x[i][j] = Bool(f"x_{i}_{j}")
    
    u = [Int(f"u_{i}") for i in range(10)]
    
    s.add(start[0] == 0, end[0] == 0)
    
    for i in range(1, 10):
        s.add(If(chosen_all[i],
                 And(start[i] >= meetings[i][3],
                     end[i] == start[i] + meetings[i][5],
                     end[i] <= meetings[i][4]),
                 True))
    
    s.add(Sum([x[i][0] for i in range(10) if i != 0]) == 0)
    
    real_chosen_exists = Or([chosen_all[i] for i in range(1,10)])
    s.add(Sum([x[0][j] for j in range(1,10)]) == If(real_chosen_exists, 1, 0))
    
    for i in range(1,10):
        s.add(Sum([x[j][i] for j in range(10) if j != i]) == If(chosen_all[i], 1, 0))
    
    total_real = Sum([If(chosen_all[i], 1, 0) for i in range(1,10)])
    s.add(total_real == Sum([If(chosen_all[i], 1, 0) for i in range(1,10)]))
    total_edges = Sum([x[i][j] for i in range(10) for j in range(10) if i != j])
    s.add(total_edges == total_real)
    
    out_degrees = [Sum([x[i][j] for j in range(10) if j != i]) for i in range(1,10)]
    s.add(Sum(out_degrees) == If(total_real > 0, total_real - 1, 0))
    for i in range(1,10):
        s.add(Sum([x[i][j] for j in range(10) if j != i]) <= 1)
        s.add(Sum([x[i][j] for j in range(10) if j != i]) >= 0)
    
    s.add(u[0] == 0)
    for i in range(1,10):
        s.add(If(chosen_all[i], And(u[i] >= 1, u[i] <= total_real), True))
    for i in range(0,10):
        for j in range(1,10):
            if i == j:
                continue
            s.add(If(x[i][j], u[j] == u[i] + 1, True))
    
    def travel_time(i, j):
        from_loc = meetings[i][2]
        to_loc = meetings[j][2]
        return travel_dict[from_loc][to_loc]
    
    for i in range(0,10):
        for j in range(1,10):
            if i == j:
                continue
            tt = travel_time(i, j)
            s.add(If(x[i][j], start[j] >= end[i] + tt, True))
    
    objective = Sum([If(chosen_all[i], 1, 0) for i in range(1,10)])
    s.maximize(objective)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 10):
            if m.evaluate(chosen_all[i]):
                start_val = m.evaluate(start[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = start_val
                end_val = m.evaluate(end[i])
                if isinstance(end_val, IntNumRef):
                    end_min = end_val.as_long()
                else:
                    end_min = end_val
                total_minutes_start = start_min
                hours_start = total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                start_time_str = f"{9+hours_start:02d}:{minutes_start:02d}"
                total_minutes_end = end_min
                hours_end = total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                end_time_str = f"{9+hours_end:02d}:{minutes_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i][1],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()