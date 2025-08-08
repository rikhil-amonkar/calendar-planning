from z3 import *
import json

# Define the locations and their indices
loc_index = {
    'Chinatown': 0,
    'Embarcadero': 1,
    'Pacific Heights': 2,
    'Russian Hill': 3,
    'Haight-Ashbury': 4,
    'Golden Gate Park': 5,
    'Fisherman\'s Wharf': 6,
    'Sunset District': 7,
    'The Castro': 8
}

# Travel times dictionary
travel_dict = {
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'The Castro'): 16,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Sunset District'): 17
}

# Create a 9x9 travel time matrix
travel = [[0]*9 for _ in range(9)]
for (from_place, to_place), t in travel_dict.items():
    i = loc_index[from_place]
    j = loc_index[to_place]
    travel[i][j] = t

# Available times (in minutes from 9:00 AM) and minimum durations
available_start = [0] * 9
available_end = [0] * 9
min_duration = [0] * 9

# Richard (Embarcadero, index1)
available_start[1] = (15-9)*60 + 15   # 3:15 PM
available_end[1] = (18-9)*60 + 45     # 6:45 PM
min_duration[1] = 90

# Mark (Pacific Heights, index2)
available_start[2] = (15-9)*60        # 3:00 PM
available_end[2] = (17-9)*60          # 5:00 PM
min_duration[2] = 45

# Matthew (Russian Hill, index3)
available_start[3] = (17-9)*60 + 30   # 5:30 PM
available_end[3] = (21-9)*60          # 9:00 PM
min_duration[3] = 90

# Rebecca (Haight-Ashbury, index4)
available_start[4] = (14-9)*60 + 45   # 2:45 PM
available_end[4] = (18-9)*60          # 6:00 PM
min_duration[4] = 60

# Melissa (Golden Gate Park, index5)
available_start[5] = (13-9)*60 + 45   # 1:45 PM
available_end[5] = (17-9)*60 + 30     # 5:30 PM
min_duration[5] = 90

# Margaret (Fisherman's Wharf, index6)
available_start[6] = (14-9)*60 + 45   # 2:45 PM
available_end[6] = (20-9)*60 + 15     # 8:15 PM
min_duration[6] = 15

# Emily (Sunset District, index7)
available_start[7] = (15-9)*60 + 45   # 3:45 PM
available_end[7] = (17-9)*60          # 5:00 PM
min_duration[7] = 45

# George (The Castro, index8)
available_start[8] = (14-9)*60        # 2:00 PM
available_end[8] = (16-9)*60 + 15     # 4:15 PM
min_duration[8] = 75

# Set up Z3 solver
s = Solver()

# Define variables: x[i][j] for i in [0..8] (start and friends) and j in [0..7] (each j corresponds to friend node j+1)
x = [ [ Bool("x_%d_%d" % (i, j)) for j in range(8) ] for i in range(9) ]

# visited[j] for j in 0..7 (corresponds to friend node j+1)
visited = [ Bool("visited_%d" % j) for j in range(8) ]

# time[i] for i in 0..8 (start and friends)
time_vars = [ Int("time_%d" % i) for i in range(9) ]

# Constraint: start time at Chinatown is 0
s.add(time_vars[0] == 0)

# For each friend j (index 0..7, corresponding to node j+1), define visited_j = exists an incoming edge
for j in range(8):
    s.add( visited[j] == Or([x[i][j] for i in range(9)]) )

# For each friend j, if visited, then exactly one incoming edge; if not, no incoming edge
for j in range(8):
    s.add( Sum([If(x[i][j], 1, 0) for i in range(9)]) == If(visited[j], 1, 0) )

# For each friend node i (node index i+1, and row index i in the x matrix for outgoing), set self-loop to false
for i in range(1, 9):  # i: node index (friend nodes are 1..8)
    # For friend node i, the column for self is j = i-1 (because j=0 corresponds to friend node1, j=1 to node2, ...)
    s.add( x[i][i-1] == False )

# Outgoing edges from start (node0): exactly one if any friend is visited, else zero
n_visited = Sum([If(visited[j], 1, 0) for j in range(8)])
visited_any = Or(visited)
s.add( Sum([x[0][j] for j in range(8)]) == If(visited_any, 1, 0) )

# Outgoing edges from friend nodes: total should be n_visited - 1 (if n_visited>0)
outgoing_total = Sum([ Sum([If(x[i][j], 1, 0) for j in range(8)]) for i in range(1,9) ])
s.add( outgoing_total == If(n_visited > 0, n_visited - 1, 0) )

# Time constraints for each friend node j (node index j+1, j in 0..7)
for j in range(8):
    node_index = j+1
    # If visited, then we have an arrival time
    arr_j = Real('arr_%d'%j)  # We use Real to avoid potential overflow, but could use Int too
    # We'll compute arr_j as the time from the predecessor plus travel time
    # Since exactly one incoming edge, we can use:
    options = []
    for i in range(9):
        # If there is an edge from i to this friend j, then arr_j = time_vars[i] + travel[i][node_index]
        options.append( If(x[i][j], time_vars[i] + travel[i][node_index], 0) )
    # But we need to pick the one that is true. We know exactly one is true? So we can do:
    # arr_j = If(x[0][j], time_vars[0] + travel[0][node_index], 
    #          If(x[1][j], time_vars[1] + travel[1][node_index], 
    #          ... ))
    # But we do it with a chain of Ifs
    arr_j_val = 0
    for i in range(9):
        arr_j_val = If(x[i][j], time_vars[i] + travel[i][node_index], arr_j_val)
    # Now, if visited, then time_vars[node_index] must be at least arr_j_val and at least available_start[node_index]
    # and time_vars[node_index] + min_duration[node_index] <= available_end[node_index]
    s.add( If(visited[j],
              And(
                  time_vars[node_index] >= arr_j_val,
                  time_vars[node_index] >= available_start[node_index],
                  time_vars[node_index] + min_duration[node_index] <= available_end[node_index]
              ),
              True) )

# Set objective to maximize the number of visited friends
objective = n_visited
s.maximize(objective)

# Solve the problem
if s.check() == sat:
    m = s.model()
    n_visited_val = m.evaluate(n_visited, model_completion=True)
    n_visited_val = n_visited_val.as_long() if is_int_value(n_visited_val) else 0
    # Reconstruct the path
    path = []
    current = 0  # start at Chinatown (node0)
    # Map to store meeting details
    meetings = []
    # Find the first meeting
    next_node_index = None
    for j in range(8):
        if m.evaluate(x[0][j]):
            next_node_index = j+1  # friend node index
            path.append(next_node_index)
            current = next_node_index
            break
    # Follow the path
    while current != None:
        found = False
        for j in range(8):
            if j != current-1:  # avoid self-loop (but we already constrained)
                if m.evaluate(x[current][j]):
                    next_node_index = j+1
                    path.append(next_node_index)
                    current = next_node_index
                    found = True
                    break
        if not found:
            break
    # Now, for each node in the path, get the start time and end time
    itinerary = []
    # Map node index to person name
    person_map = {
        1: "Richard",
        2: "Mark",
        3: "Matthew",
        4: "Rebecca",
        5: "Melissa",
        6: "Margaret",
        7: "Emily",
        8: "George"
    }
    for node in path:
        start_time_min = m.evaluate(time_vars[node])
        if isinstance(start_time_min, IntNumRef):
            start_time_min = start_time_min.as_long()
        else:
            start_time_min = 0  # fallback, though should not happen
        end_time_min = start_time_min + min_duration[node]
        # Convert to time string from 9:00 AM
        total_minutes_start = start_time_min
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time_str = f"{hours_start:02d}:{minutes_start:02d}"
        total_minutes_end = end_time_min
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
        itinerary.append({
            "action": "meet",
            "person": person_map[node],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    # Output the itinerary in the required format
    print("SOLUTION:")
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print("No solution found")