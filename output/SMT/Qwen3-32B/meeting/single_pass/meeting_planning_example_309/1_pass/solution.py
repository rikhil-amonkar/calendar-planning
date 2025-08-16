from z3 import *
import json

# Define the solver
s = Optimize()

# Define variables for each step
active_1, active_2, active_3 = Bools('active_1 active_2 active_3')
friend_1, friend_2, friend_3 = Ints('friend_1 friend_2 friend_3')
start_1, start_2, start_3 = Ints('start_1 start_2 start_3')
end_1, end_2, end_3 = Ints('end_1 end_2 end_3')

# Step 1 constraints
location_1 = If(friend_1 == 0, 1, If(friend_1 == 1, 2, 3))
travel_time_1 = If(location_1 == 1, 5, If(location_1 == 2, 17, 19))
arrival_time_1 = 540 + travel_time_1
s.add(Implies(active_1, And(
    friend_1 >= 0, friend_1 <= 2,
    start_1 >= arrival_time_1,
    end_1 == start_1 + If(friend_1 == 0, 90, If(friend_1 == 1, 75, 45)),
    start_1 >= If(friend_1 == 0, 570, If(friend_1 == 1, 420, 675)),
    end_1 <= If(friend_1 == 0, 810, If(friend_1 == 1, 1260, 825))
)))

# Step 2 constraints
previous_location_2 = If(active_1, location_1, 0)
previous_end_2 = If(active_1, end_1, 540)
location_2 = If(friend_2 == 0, 1, If(friend_2 == 1, 2, 3))

travel_time_2 = If(previous_location_2 == 0,
    If(location_2 == 1, 5,
        If(location_2 == 2, 17,
            If(location_2 == 3, 19, 0))),
    If(previous_location_2 == 1,
        If(location_2 == 1, 5,
            If(location_2 == 2, 17,
                If(location_2 == 3, 22, 0))),
        If(previous_location_2 == 2,
            If(location_2 == 0, 17,
                If(location_2 == 1, 16,
                    If(location_2 == 3, 16, 0))),
            If(previous_location_2 == 3,
                If(location_2 == 0, 19,
                    If(location_2 == 1, 18,
                        If(location_2 == 2, 16, 0))),
                0))))
arrival_time_2 = previous_end_2 + travel_time_2
s.add(Implies(active_2, And(
    friend_2 >= 0, friend_2 <= 2,
    start_2 >= arrival_time_2,
    end_2 == start_2 + If(friend_2 == 0, 90, If(friend_2 == 1, 75, 45)),
    start_2 >= If(friend_2 == 0, 570, If(friend_2 == 1, 420, 675)),
    end_2 <= If(friend_2 == 0, 810, If(friend_2 == 1, 1260, 825))
)))

# Step 3 constraints
previous_location_3 = If(active_2, location_2, If(active_1, location_1, 0))
previous_end_3 = If(active_2, end_2, If(active_1, end_1, 540))
location_3 = If(friend_3 == 0, 1, If(friend_3 == 1, 2, 3))

travel_time_3 = If(previous_location_3 == 0,
    If(location_3 == 1, 5,
        If(location_3 == 2, 17,
            If(location_3 == 3, 19, 0))),
    If(previous_location_3 == 1,
        If(location_3 == 1, 5,
            If(location_3 == 2, 17,
                If(location_3 == 3, 22, 0))),
        If(previous_location_3 == 2,
            If(location_3 == 0, 17,
                If(location_3 == 1, 16,
                    If(location_3 == 3, 16, 0))),
            If(previous_location_3 == 3,
                If(location_3 == 0, 19,
                    If(location_3 == 1, 18,
                        If(location_3 == 2, 16, 0))),
                0))))
arrival_time_3 = previous_end_3 + travel_time_3
s.add(Implies(active_3, And(
    friend_3 >= 0, friend_3 <= 2,
    start_3 >= arrival_time_3,
    end_3 == start_3 + If(friend_3 == 0, 90, If(friend_3 == 1, 75, 45)),
    start_3 >= If(friend_3 == 0, 570, If(friend_3 == 1, 420, 675)),
    end_3 <= If(friend_3 == 0, 810, If(friend_3 == 1, 1260, 825))
)))

# Ensure each friend is met at most once
nancy_count = If(And(active_1, friend_1 == 0), 1, 0) + If(And(active_2, friend_2 == 0), 1, 0) + If(And(active_3, friend_3 == 0), 1, 0)
s.add(nancy_count <= 1)
mary_count = If(And(active_1, friend_1 == 1), 1, 0) + If(And(active_2, friend_2 == 1), 1, 0) + If(And(active_3, friend_3 == 1), 1, 0)
s.add(mary_count <= 1)
jessica_count = If(And(active_1, friend_1 == 2), 1, 0) + If(And(active_2, friend_2 == 2), 1, 0) + If(And(active_3, friend_3 == 2), 1, 0)
s.add(jessica_count <= 1)

# Maximize the number of active steps
total_active = If(active_1, 1, 0) + If(active_2, 1, 0) + If(active_3, 1, 0)
s.maximize(total_active)

# Check the model
if s.check() == sat:
    model = s.model()
    itinerary = []
    friends = [friend_1, friend_2, friend_3]
    starts = [start_1, start_2, start_3]
    ends = [end_1, end_2, end_3]
    actives = [active_1, active_2, active_3]
    for i in range(3):
        active = model.eval(actives[i])
        if is_true(active):
            person_code = model.eval(friends[i]).as_long()
            start_time = model.eval(starts[i]).as_long()
            end_time = model.eval(ends[i]).as_long()
            person_name = ['Nancy', 'Mary', 'Jessica'][person_code]
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            itinerary.append({
                "action": "meet",
                "person": person_name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")