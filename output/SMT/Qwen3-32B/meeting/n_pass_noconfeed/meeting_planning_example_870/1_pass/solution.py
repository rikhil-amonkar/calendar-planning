from z3 import *
import json

# Define all locations and their indices
all_locations = ['Pacific Heights', 'Marina District', 'The Castro', 'Richmond District', 'Alamo Square', 'Financial District', 'Presidio', 'Mission District', 'Nob Hill', 'Russian Hill']

# Travel time matrix (10x10)
travel_time = [[0]*10 for _ in range(10)]

# Populate travel_time based on the problem statement
# Pacific Heights to others
travel_time[0][1] = 6
travel_time[0][2] = 16
travel_time[0][3] = 12
travel_time[0][4] = 10
travel_time[0][5] = 13
travel_time[0][6] = 11
travel_time[0][7] = 15
travel_time[0][8] = 8
travel_time[0][9] = 7

# Marina District to others
travel_time[1][0] = 7
travel_time[1][2] = 22
travel_time[1][3] = 11
travel_time[1][4] = 15
travel_time[1][5] = 17
travel_time[1][6] = 10
travel_time[1][7] = 20
travel_time[1][8] = 12
travel_time[1][9] = 8

# The Castro to others
travel_time[2][0] = 16
travel_time[2][1] = 21
travel_time[2][3] = 16
travel_time[2][4] = 8
travel_time[2][5] = 21
travel_time[2][6] = 20
travel_time[2][7] = 7
travel_time[2][8] = 16
travel_time[2][9] = 18

# Richmond District to others
travel_time[3][0] = 10
travel_time[3][1] = 9
travel_time[3][2] = 16
travel_time[3][4] = 13
travel_time[3][5] = 22
travel_time[3][6] = 7
travel_time[3][7] = 20
travel_time[3][8] = 17
travel_time[3][9] = 13

# Alamo Square to others
travel_time[4][0] = 10
travel_time[4][1] = 15
travel_time[4][2] = 8
travel_time[4][3] = 11
travel_time[4][5] = 17
travel_time[4][6] = 17
travel_time[4][7] = 10
travel_time[4][8] = 11
travel_time[4][9] = 13

# Financial District to others
travel_time[5][0] = 13
travel_time[5][1] = 15
travel_time[5][2] = 20
travel_time[5][3] = 21
travel_time[5][4] = 17
travel_time[5][6] = 22
travel_time[5][7] = 17
travel_time[5][8] = 8
travel_time[5][9] = 11

# Presidio to others
travel_time[6][0] = 11
travel_time[6][1] = 11
travel_time[6][2] = 21
travel_time[6][3] = 7
travel_time[6][4] = 19
travel_time[6][5] = 23
travel_time[6][7] = 25
travel_time[6][8] = 18
travel_time[6][9] = 14

# Mission District to others
travel_time[7][0] = 16
travel_time[7][1] = 19
travel_time[7][2] = 7
travel_time[7][3] = 20
travel_time[7][4] = 11
travel_time[7][5] = 15
travel_time[7][6] = 25
travel_time[7][8] = 12
travel_time[7][9] = 15

# Nob Hill to others
travel_time[8][0] = 8
travel_time[8][1] = 11
travel_time[8][2] = 17
travel_time[8][3] = 14
travel_time[8][4] = 11
travel_time[8][5] = 9
travel_time[8][6] = 17
travel_time[8][7] = 13
travel_time[8][9] = 5

# Russian Hill to others
travel_time[9][0] = 7
travel_time[9][1] = 7
travel_time[9][2] = 21
travel_time[9][3] = 14
travel_time[9][4] = 15
travel_time[9][5] = 11
travel_time[9][6] = 14
travel_time[9][7] = 16
travel_time[9][8] = 5

# Friends data
friends = ['Carol', 'Sandra', 'Brian', 'Kimberly', 'Kenneth', 'Linda', 'Laura', 'Karen', 'Paul']
friends_loc = [5, 8, 6, 3, 2, 1, 7, 9, 4]
friends_available_start = [615, 555, 600, 855, 945, 1020, 1035, 1110, 1140]
friends_available_end = [720, 1170, 1110, 1200, 1035, 1380, 1050, 1380, 1170]
friends_min_duration = [60, 60, 75, 30, 30, 30, 30, 75, 15]

# Create solver
solver = Optimize()

# Create variables
met = [Bool(f"met_{i}") for i in range(9)]
start = [Int(f"start_{i}") for i in range(9)]
end = [Int(f"end_{i}") for i in range(9)]

# Add constraints for each friend
for i in range(9):
    # If met[i] is true, then start >= 540 + travel_time from PH to location
    solver.add(Implies(met[i], start[i] >= 540 + travel_time[0][friends_loc[i]]))
    # start >= available start
    solver.add(Implies(met[i], start[i] >= friends_available_start[i]))
    # end <= available end
    solver.add(Implies(met[i], end[i] <= friends_available_end[i]))
    # end - start >= min_duration
    solver.add(Implies(met[i], end[i] - start[i] >= friends_min_duration[i]))

# Add pairwise constraints for all pairs of friends
for i in range(9):
    for j in range(i+1, 9):
        loc_i = friends_loc[i]
        loc_j = friends_loc[j]
        travel_ij = travel_time[loc_i][loc_j]
        travel_ji = travel_time[loc_j][loc_i]
        constraint = Implies(And(met[i], met[j]), Or(
            And(start[j] >= end[i] + travel_ij),
            And(start[i] >= end[j] + travel_ji)
        ))
        solver.add(constraint)

# Add goal to maximize the number of met friends
solver.maximize(Sum([If(met[i], 1, 0) for i in range(9)]))

# Check if the problem is satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the met friends and their meeting times
    itinerary = []
    for i in range(9):
        if is_true(model.evaluate(met[i])):
            start_time = model.evaluate(start[i])
            end_time = model.evaluate(end[i])
            # Convert to H:MM format
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            start_str = f"{start_h}:{start_m:02d}"
            end_str = f"{end_h}:{end_m:02d}"
            person = friends[i]
            location = all_locations[friends_loc[i]]
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")