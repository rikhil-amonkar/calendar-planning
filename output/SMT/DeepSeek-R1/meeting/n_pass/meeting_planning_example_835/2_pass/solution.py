import z3

# Sample data - replace with actual input
num_agents = 2
num_meetings = 3
num_locations = 4
travel_time = [[0, 1, 2, 3], [1, 0, 1, 2], [2, 1, 0, 1], [3, 2, 1, 0]]
current_location = [0, 1]
current_time = [0, 0]
duration = [1, 1, 1]
location = [0, 1, 2]
earliest_start = [0, 0, 0]
latest_start = [10, 10, 10]

s = z3.Solver()

# Assignment variables: assignment[i][j] indicates if meeting j is assigned to agent i
assignment = [[z3.Bool(f"assignment_{i}_{j}") for j in range(num_meetings)] 
              for i in range(num_agents)]

# Start time variables for each meeting
start = [z3.Int(f"start_{j}") for j in range(num_meetings)]

# Constraint: Each meeting assigned to exactly one agent
for j in range(num_meetings):
    s.add(z3.Or([assignment[i][j] for i in range(num_agents)]))
    s.add(z3.AtMost(*[assignment[i][j] for i in range(num_agents)], 1))

# Constraint: Meeting time windows
for j in range(num_meetings):
    s.add(start[j] >= earliest_start[j])
    s.add(start[j] <= latest_start[j])

# Define Z3 arrays for meeting properties
start_array = z3.Array('start_array', z3.IntSort(), z3.IntSort())
duration_array = z3.Array('duration_array', z3.IntSort(), z3.IntSort())
location_array = z3.Array('location_array', z3.IntSort(), z3.IntSort())
for j in range(num_meetings):
    s.add(start_array[j] == start[j])
    s.add(duration_array[j] == duration[j])
    s.add(location_array[j] == location[j])

# Define travel time array
travel_array = z3.Array('travel_array', z3.IntSort(), z3.IntSort(), z3.IntSort())
for loc1 in range(num_locations):
    for loc2 in range(num_locations):
        s.add(travel_array[loc1, loc2] == travel_time[loc1][loc2])

# Sequence variables: seq[i][k] = meeting ID at position k of agent i's schedule (-1 for empty)
seq = [[z3.Int(f"seq_{i}_{k}") for k in range(num_meetings)] 
       for i in range(num_agents)]

# Sequence constraints
for i in range(num_agents):
    for k in range(num_meetings):
        s.add(seq[i][k] >= -1)
        s.add(seq[i][k] < num_meetings)

# Meeting assignment constraints
for i in range(num_agents):
    for j in range(num_meetings):
        count = z3.Sum([z3.If(seq[i][k] == j, 1, 0) for k in range(num_meetings)])
        s.add(z3.Implies(assignment[i][j], count == 1))
        s.add(z3.Implies(z3.Not(assignment[i][j]), count == 0))

# Contiguous sequence constraint
for i in range(num_agents):
    for k in range(num_meetings - 1):
        s.add(z3.Implies(seq[i][k] == -1, seq[i][k + 1] == -1))

# Travel time constraints between consecutive meetings
for i in range(num_agents):
    for k in range(num_meetings - 1):
        meeting_k = seq[i][k]
        meeting_k1 = seq[i][k + 1]
        cond = z3.And(meeting_k != -1, meeting_k1 != -1)
        
        start_k = start_array[meeting_k]
        start_k1 = start_array[meeting_k1]
        dur_k = duration_array[meeting_k]
        loc_k = location_array[meeting_k]
        loc_k1 = location_array[meeting_k1]
        travel_needed = travel_array[loc_k, loc_k1]
        
        s.add(z3.Implies(cond, start_k1 >= start_k + dur_k + travel_needed))

# First meeting constraints
for i in range(num_agents):
    meeting0 = seq[i][0]
    cond = (meeting0 != -1)
    
    loc0 = location_array[meeting0]
    travel_needed = travel_array[current_location[i], loc0]
    start0 = start_array[meeting0]
    
    s.add(z3.Implies(cond, start0 >= current_time[i] + travel_needed))

# Check and print solution
if s.check() == z3.sat:
    m = s.model()
    for i in range(num_agents):
        print(f"Agent {i}:")
        for k in range(num_meetings):
            meeting_id = m[seq[i][k]].as_long()
            if meeting_id != -1:
                start_time = m[start[meeting_id]]
                print(f"  Meeting {meeting_id} starts at {start_time}")
else:
    print("No solution found")