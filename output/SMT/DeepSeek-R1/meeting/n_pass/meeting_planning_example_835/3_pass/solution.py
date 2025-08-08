import z3
import sys

def main():
    data = sys.stdin.read().split()
    if not data:
        return
    
    num_agents = int(data[0])
    num_meetings = int(data[1])
    num_locations = int(data[2])
    index = 3
    
    travel_time = []
    for i in range(num_locations):
        row = list(map(int, data[index:index+num_locations]))
        travel_time.append(row)
        index += num_locations
        
    current_location = list(map(int, data[index:index+num_agents]))
    index += num_agents
    
    current_time = list(map(int, data[index:index+num_agents]))
    index += num_agents
    
    duration = list(map(int, data[index:index+num_meetings]))
    index += num_meetings
    
    location = list(map(int, data[index:index+num_meetings]))
    index += num_meetings
    
    earliest_start = list(map(int, data[index:index+num_meetings]))
    index += num_meetings
    
    latest_start = list(map(int, data[index:index+num_meetings]))
    index += num_meetings

    s = z3.Solver()

    assignment = [[z3.Bool(f"assignment_{i}_{j}") for j in range(num_meetings)] 
                for i in range(num_agents)]
    start = [z3.Int(f"start_{j}") for j in range(num_meetings)]

    for j in range(num_meetings):
        s.add(z3.Or([assignment[i][j] for i in range(num_agents)]))
        s.add(z3.AtMost(*[assignment[i][j] for i in range(num_agents)], 1))

    for j in range(num_meetings):
        s.add(start[j] >= earliest_start[j])
        s.add(start[j] <= latest_start[j])

    start_array = z3.Array('start_array', z3.IntSort(), z3.IntSort())
    duration_array = z3.Array('duration_array', z3.IntSort(), z3.IntSort())
    location_array = z3.Array('location_array', z3.IntSort(), z3.IntSort())
    for j in range(num_meetings):
        s.add(start_array[j] == start[j])
        s.add(duration_array[j] == duration[j])
        s.add(location_array[j] == location[j])

    travel_array = z3.Array('travel_array', z3.IntSort(), z3.IntSort(), z3.IntSort())
    for loc1 in range(num_locations):
        for loc2 in range(num_locations):
            s.add(travel_array[loc1, loc2] == travel_time[loc1][loc2])

    seq = [[z3.Int(f"seq_{i}_{k}") for k in range(num_meetings)] 
            for i in range(num_agents)]

    for i in range(num_agents):
        for k in range(num_meetings):
            s.add(seq[i][k] >= -1)
            s.add(seq[i][k] < num_meetings)

    for i in range(num_agents):
        for j in range(num_meetings):
            count = z3.Sum([z3.If(seq[i][k] == j, 1, 0) for k in range(num_meetings)])
            s.add(z3.Implies(assignment[i][j], count == 1))
            s.add(z3.Implies(z3.Not(assignment[i][j]), count == 0))

    for i in range(num_agents):
        for k in range(num_meetings - 1):
            s.add(z3.Implies(seq[i][k] == -1, seq[i][k+1] == -1))

    for i in range(num_agents):
        for k in range(num_meetings - 1):
            meeting_k = seq[i][k]
            meeting_k1 = seq[i][k+1]
            cond = z3.And(meeting_k != -1, meeting_k1 != -1)
            
            start_k = start_array[meeting_k]
            start_k1 = start_array[meeting_k1]
            dur_k = duration_array[meeting_k]
            loc_k = location_array[meeting_k]
            loc_k1 = location_array[meeting_k1]
            travel_needed = travel_array[loc_k, loc_k1]
            
            s.add(z3.Implies(cond, start_k1 >= start_k + dur_k + travel_needed))

    for i in range(num_agents):
        meeting0 = seq[i][0]
        cond = (meeting0 != -1)
        loc0 = location_array[meeting0]
        travel_needed = travel_array[current_location[i], loc0]
        start0 = start_array[meeting0]
        s.add(z3.Implies(cond, start0 >= current_time[i] + travel_needed))

    if s.check() == z3.sat:
        m = s.model()
        for i in range(num_agents):
            print(f"Agent {i}:")
            agent_has_meetings = False
            for k in range(num_meetings):
                meeting_id_val = m.evaluate(seq[i][k], model_completion=True)
                if meeting_id_val.as_long() != -1:
                    agent_has_meetings = True
                    meeting_index = meeting_id_val.as_long()
                    start_val = m.evaluate(start[meeting_index], model_completion=True)
                    print(f"  Meeting {meeting_index} starts at {start_val}")
            if not agent_has_meetings:
                print("  No meetings")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()