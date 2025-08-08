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
    
    # Parse travel_time matrix
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

    # Assignment variables: assignment[i][j] indicates if meeting j is assigned to agent i
    assignment = [[z3.Bool(f"assignment_{i}_{j}") for j in range(num_meetings)] 
                for i in range(num_agents)]
    
    # Start time variables for each meeting
    start = [z3.Int(f"start_{j}") for j in range(num_meetings)]
    
    # Each meeting assigned to exactly one agent
    for j in range(num_meetings):
        s.add(z3.Or([assignment[i][j] for i in range(num_agents)]))
        s.add(z3.AtMost(*[assignment[i][j] for i in range(num_agents)], 1))
    
    # Meeting time windows
    for j in range(num_meetings):
        s.add(start[j] >= earliest_start[j])
        s.add(start[j] <= latest_start[j])
    
    # Sequence variables: seq[i][k] = meeting at position k of agent i (-1 if none)
    seq = [[z3.Int(f"seq_{i}_{k}") for k in range(num_meetings)] 
            for i in range(num_agents)]
    
    # Sequence constraints
    for i in range(num_agents):
        for k in range(num_meetings):
            s.add(seq[i][k] >= -1)
            s.add(seq[i][k] < num_meetings)
    
    # Assignment-consistency constraints
    for i in range(num_agents):
        for j in range(num_meetings):
            in_sequence = z3.Or([seq[i][k] == j for k in range(num_meetings)])
            s.add(assignment[i][j] == in_sequence)
    
    # Contiguous sequence constraint
    for i in range(num_agents):
        for k in range(num_meetings - 1):
            s.add(z3.Implies(seq[i][k] == -1, seq[i][k+1] == -1))
    
    # Precompute Z3 integer values for travel times
    travel_z3 = [[z3.IntVal(travel_time[i][j]) for j in range(num_locations)] 
                for i in range(num_locations)]
    
    # Travel time constraints between consecutive meetings
    for i in range(num_agents):
        for k in range(num_meetings - 1):
            m1 = seq[i][k]
            m2 = seq[i][k+1]
            cond = z3.And(m1 != -1, m2 != -1)
            
            # Inline property lookups using conditional expressions
            start1 = z3.Sum([z3.If(m1 == j, start[j], 0) for j in range(num_meetings)])
            dur1 = z3.Sum([z3.If(m1 == j, duration[j], 0) for j in range(num_meetings)])
            loc1 = z3.Sum([z3.If(m1 == j, location[j], 0) for j in range(num_meetings)])
            
            start2 = z3.Sum([z3.If(m2 == j, start[j], 0) for j in range(num_meetings)])
            loc2 = z3.Sum([z3.If(m2 == j, location[j], 0) for j in range(num_meetings)])
            
            # Get travel time using conditional expressions
            travel_needed = z3.Sum([
                z3.If(z3.And(loc1 == idx_i, loc2 == idx_j), travel_z3[idx_i][idx_j], 0)
                for idx_i in range(num_locations)
                for idx_j in range(num_locations)
            ])
            
            s.add(z3.Implies(cond, start2 >= start1 + dur1 + travel_needed))
    
    # First meeting constraints
    for i in range(num_agents):
        m0 = seq[i][0]
        cond = (m0 != -1)
        
        start0 = z3.Sum([z3.If(m0 == j, start[j], 0) for j in range(num_meetings)])
        loc0 = z3.Sum([z3.If(m0 == j, location[j], 0) for j in range(num_meetings)])
        
        # Get travel time from current location to first meeting
        travel_needed = z3.Sum([
            z3.If(z3.And(current_location[i] == idx_i, loc0 == idx_j), 
                  travel_z3[idx_i][idx_j], 0)
            for idx_i in range(num_locations)
            for idx_j in range(num_locations)
        ])
        
        s.add(z3.Implies(cond, start0 >= current_time[i] + travel_needed))
    
    # Set a timeout to prevent hanging (30000 ms = 30 seconds)
    s.set("timeout", 30000)
    
    # Solve and print results
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