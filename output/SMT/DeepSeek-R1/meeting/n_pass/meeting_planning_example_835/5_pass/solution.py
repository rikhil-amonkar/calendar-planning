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

    # Assignment variables: assignment[i][j] = True if meeting j is assigned to agent i
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
    
    # For each agent, ensure meetings don't overlap and have travel time
    for i in range(num_agents):
        # Get meetings assigned to this agent
        agent_meetings = [j for j in range(num_meetings)]
        
        # Create ordering variable for each meeting: order[i][j] = position in agent's schedule
        order = [z3.Int(f"order_{i}_{j}") for j in range(num_meetings)]
        for j in range(num_meetings):
            s.add(z3.Implies(assignment[i][j], order[j] >= 0))
            s.add(z3.Implies(z3.Not(assignment[i][j]), order[j] == -1))
            s.add(order[j] < num_meetings)
        
        # All assigned meetings have distinct positive order positions
        for j1 in range(num_meetings):
            for j2 in range(j1+1, num_meetings):
                s.add(z3.Implies(z3.And(assignment[i][j1], assignment[i][j2]), 
                                 order[j1] != order[j2]))
        
        # Constraint: if meeting j1 is before j2 in agent's schedule, then
        # start[j2] >= start[j1] + duration[j1] + travel_time[location[j1]][location[j2]]
        for j1 in range(num_meetings):
            for j2 in range(num_meetings):
                if j1 == j2:
                    continue
                # If both meetings assigned to agent i and j1 comes before j2
                cond = z3.And(assignment[i][j1], assignment[i][j2], order[j1] < order[j2])
                travel = travel_time[location[j1]][location[j2]]
                s.add(z3.Implies(cond, 
                                 start[j2] >= start[j1] + duration[j1] + travel))
        
        # First meeting constraint: must have time to travel from current location
        for j in range(num_meetings):
            cond = assignment[i][j]
            travel_needed = travel_time[current_location[i]][location[j]]
            s.add(z3.Implies(cond, start[j] >= current_time[i] + travel_needed))
    
    # Set timeout to prevent indefinite hangs
    s.set("timeout", 30000)
    
    # Solve and output results
    if s.check() == z3.sat:
        m = s.model()
        # For each agent, collect meetings and sort by start time
        agent_schedules = [[] for _ in range(num_agents)]
        for j in range(num_meetings):
            start_val = m.evaluate(start[j], model_completion=True).as_long()
            for i in range(num_agents):
                if m.evaluate(assignment[i][j], model_completion=True):
                    agent_schedules[i].append((j, start_val))
        
        # Output each agent's meetings sorted by start time
        for i in range(num_agents):
            print(f"Agent {i}:")
            if not agent_schedules[i]:
                print("  No meetings")
            else:
                # Sort meetings by start time
                agent_schedules[i].sort(key=lambda x: x[1])
                for meeting, start_time in agent_schedules[i]:
                    print(f"  Meeting {meeting} starts at {start_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()