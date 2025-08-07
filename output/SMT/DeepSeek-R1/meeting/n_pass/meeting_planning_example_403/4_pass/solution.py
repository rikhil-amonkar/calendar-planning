import itertools
from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    travel_times = [
        ("Union Square", "Golden Gate Park", 22),
        ("Union Square", "Pacific Heights", 15),
        ("Union Square", "Presidio", 24),
        ("Union Square", "Chinatown", 7),
        ("Union Square", "The Castro", 19),
        ("Golden Gate Park", "Union Square", 22),
        ("Golden Gate Park", "Pacific Heights", 16),
        ("Golden Gate Park", "Presidio", 11),
        ("Golden Gate Park", "Chinatown", 23),
        ("Golden Gate Park", "The Castro", 13),
        ("Pacific Heights", "Union Square", 12),
        ("Pacific Heights", "Golden Gate Park", 15),
        ("Pacific Heights", "Presidio", 11),
        ("Pacific Heights", "Chinatown", 11),
        ("Pacific Heights", "The Castro", 16),
        ("Presidio", "Union Square", 22),
        ("Presidio", "Golden Gate Park", 12),
        ("Presidio", "Pacific Heights", 11),
        ("Presidio", "Chinatown", 21),
        ("Presidio", "The Castro", 21),
        ("Chinatown", "Union Square", 7),
        ("Chinatown", "Golden Gate Park", 23),
        ("Chinatown", "Pacific Heights", 10),
        ("Chinatown", "Presidio", 19),
        ("Chinatown", "The Castro", 22),
        ("The Castro", "Union Square", 19),
        ("The Castro", "Golden Gate Park", 11),
        ("The Castro", "Pacific Heights", 16),
        ("The Castro", "Presidio", 20),
        ("The Castro", "Chinatown", 20)
    ]
    
    travel_time_dict = {}
    for (from_loc, to_loc, time) in travel_times:
        travel_time_dict[(from_loc, to_loc)] = time

    friends = [
        ('Andrew', 'Golden Gate Park', 11*60+45, 14*60+30, 75),
        ('Sarah', 'Pacific Heights', 16*60+15, 18*60+45, 15),
        ('Nancy', 'Presidio', 17*60+30, 19*60+15, 60),
        ('Rebecca', 'Chinatown', 9*60+45, 21*60+30, 90),
        ('Robert', 'The Castro', 8*60+30, 14*60+15, 30)
    ]
    n_friends = len(friends)
    indices = list(range(n_friends))
    
    found = False
    result_schedule = []
    
    for size in range(n_friends, 0, -1):
        subsets = list(itertools.combinations(indices, size))
        for subset in subsets:
            n = size
            if n == 0:
                continue
                
            locations = ['Union Square']
            availability_start = [540]
            availability_end = [540]
            min_time_list = [0]
            friend_names = ['Start']
            for idx in subset:
                friend_data = friends[idx]
                locations.append(friend_data[1])
                availability_start.append(friend_data[2])
                availability_end.append(friend_data[3])
                min_time_list.append(friend_data[4])
                friend_names.append(friend_data[0])
            
            s = Solver()
            num_nodes = n + 1
            b = [[Bool(f"b_{i}_{j}") for j in range(num_nodes)] for i in range(num_nodes)]
            u = [Int(f"u_{i}") for i in range(num_nodes)]
            A = [Int(f"A_{i}") for i in range(num_nodes)]
            D = [Int(f"D_{i}") for i in range(num_nodes)]
            S = [Int(f"S_{i}") for i in range(num_nodes)]
            
            s.add(u[0] == 0)
            s.add(A[0] == 540)
            s.add(D[0] == 540)
            s.add(S[0] == 540)
            
            start_outgoing = [If(b[0][j], 1, 0) for j in range(1, num_nodes)]
            s.add(Sum(start_outgoing) == 1)
            
            for j in range(1, num_nodes):
                incoming = [If(b[i][j], 1, 0) for i in range(0, num_nodes) if i != j]
                s.add(Sum(incoming) == 1)
                
            for i in range(1, num_nodes):
                outgoing = [If(b[i][j], 1, 0) for j in range(1, num_nodes) if i != j]
                s.add(Sum(outgoing) == 1)
                
            for i in range(0, num_nodes):
                for j in range(0, num_nodes):
                    if i == j:
                        s.add(b[i][j] == False)
            
            for i in range(0, num_nodes):
                s.add(u[i] >= 0, u[i] <= n)
                for j in range(1, num_nodes):
                    if i != j:
                        s.add(Implies(b[i][j], u[j] == u[i] + 1))
            
            for j in range(1, num_nodes):
                s.add(S[j] == If(A[j] >= availability_start[j], A[j], availability_start[j]))
                s.add(D[j] == S[j] + min_time_list[j])
                s.add(D[j] <= availability_end[j])
                s.add(A[j] >= 0)
                s.add(S[j] >= 0)
                s.add(D[j] >= 0)
                
            for i in range(0, num_nodes):
                for j in range(1, num_nodes):
                    if i != j:
                        tt = travel_time_dict.get((locations[i], locations[j]))
                        if tt is None:
                            tt = 1000
                        s.add(Implies(b[i][j], A[j] >= D[i] + tt))
            
            if s.check() == sat:
                m = s.model()
                schedule_entries = []
                for j in range(1, num_nodes):
                    a_val = m.evaluate(A[j]).as_long()
                    s_val = m.evaluate(S[j]).as_long()
                    d_val = m.evaluate(D[j]).as_long()
                    friend_name = friend_names[j]
                    start_str = min_to_time(s_val)
                    end_str = min_to_time(d_val)
                    schedule_entries.append({
                        "action": "meet",
                        "person": friend_name,
                        "start_time": start_str,
                        "end_time": end_str
                    })
                schedule_entries.sort(key=lambda x: x['start_time'])
                result_schedule = schedule_entries
                found = True
                break
        if found:
            break
            
    if not found:
        result_schedule = []
        
    output = {"itinerary": result_schedule}
    print("SOLUTION:")
    print(output)

if __name__ == "__main__":
    main()