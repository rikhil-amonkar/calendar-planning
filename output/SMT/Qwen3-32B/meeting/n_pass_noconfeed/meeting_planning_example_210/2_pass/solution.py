import z3
import json

# Define the friends and their constraints
# 0: Emily (Presidio)
# 1: Joseph (Richmond District)
# 2: Melissa (Financial District)

# Earliest and latest available times (in minutes since midnight)
earliest = {
    0: 975,  # Emily
    1: 1035, # Joseph
    2: 945   # Melissa
}

latest = {
    0: 1080, # Emily
    1: 1320, # Joseph
    2: 1305  # Melissa
}

min_duration = {
    0: 105, # Emily
    1: 120, # Joseph
    2: 75   # Melissa
}

# Travel times between locations (start, end): time in minutes
# Locations are 0: Fisherman's Wharf (start), 1: Presidio, 2: Richmond, 3: Financial
travel_times = {
    (0,1): 17, (0,2):18, (0,3):11,
    (1,0):19, (1,2):7, (1,3):23,
    (2,0):18, (2,1):7, (2,3):22,
    (3,0):10, (3,1):22, (3,2):21
}

# Create solver
s = z3.Solver()

# Variables for order: first, second, third (each 0,1,2)
first, second, third = z3.Ints('first second third')

# Add constraints that first, second, third are distinct and in 0-2
s.add(z3.Distinct(first, second, third))
s.add(z3.And(first >= 0, first <= 2))
s.add(z3.And(second >= 0, second <= 2))
s.add(z3.And(third >= 0, third <= 2))

# Variables for start and end times of each friend
start_E, end_E = z3.Ints('start_E end_E')
start_J, end_J = z3.Ints('start_J end_J')
start_M, end_M = z3.Ints('start_M end_M')

# First friend's constraints
arrival_time_first = 540 + z3.If(first == 0, 17, z3.If(first == 1, 18, 11))

s.add(z3.Implies(first == 0, start_E >= z3.If(arrival_time_first >= earliest[0], arrival_time_first, earliest[0])))
s.add(z3.Implies(first == 0, end_E == start_E + min_duration[0]))
s.add(z3.Implies(first == 0, end_E <= latest[0]))

s.add(z3.Implies(first == 1, start_J >= z3.If(arrival_time_first >= earliest[1], arrival_time_first, earliest[1])))
s.add(z3.Implies(first == 1, end_J == start_J + min_duration[1]))
s.add(z3.Implies(first == 1, end_J <= latest[1]))

s.add(z3.Implies(first == 2, start_M >= z3.If(arrival_time_first >= earliest[2], arrival_time_first, earliest[2])))
s.add(z3.Implies(first == 2, end_M == start_M + min_duration[2]))
s.add(z3.Implies(first == 2, end_M <= latest[2]))

# Define first_loc and second_loc
first_loc = z3.If(first == 0, 1, z3.If(first == 1, 2, 3))
second_loc = z3.If(second == 0, 1, z3.If(second == 1, 2, 3))

# Compute travel_time_step2
travel_time_step2 = z3.If(
    first_loc == 1,
    z3.If(second_loc == 2, 7, 23),
    z3.If(first_loc == 2,
          z3.If(second_loc == 1, 7, 22),
          z3.If(second_loc == 1, 22, 21)
          )
)

end_time_first = z3.If(first == 0, end_E, z3.If(first == 1, end_J, end_M))
arrival_time_second = end_time_first + travel_time_step2

# Add constraints for the second friend
s.add(z3.Implies(second == 0, start_E >= z3.If(arrival_time_second >= earliest[0], arrival_time_second, earliest[0])))
s.add(z3.Implies(second == 0, end_E == start_E + min_duration[0]))
s.add(z3.Implies(second == 0, end_E <= latest[0]))

s.add(z3.Implies(second == 1, start_J >= z3.If(arrival_time_second >= earliest[1], arrival_time_second, earliest[1])))
s.add(z3.Implies(second == 1, end_J == start_J + min_duration[1]))
s.add(z3.Implies(second == 1, end_J <= latest[1]))

s.add(z3.Implies(second == 2, start_M >= z3.If(arrival_time_second >= earliest[2], arrival_time_second, earliest[2])))
s.add(z3.Implies(second == 2, end_M == start_M + min_duration[2]))
s.add(z3.Implies(second == 2, end_M <= latest[2]))

# Define third_loc
third_loc = z3.If(third == 0, 1, z3.If(third == 1, 2, 3))

# Compute travel_time_step3
travel_time_step3 = z3.If(
    second_loc == 1,
    z3.If(third_loc == 2, 7, z3.If(third_loc == 3, 23, 0)),
    z3.If(
        second_loc == 2,
        z3.If(third_loc == 1, 7, z3.If(third_loc == 3, 22, 0)),
        z3.If(
            second_loc == 3,
            z3.If(third_loc == 1, 22, z3.If(third_loc == 2, 21, 0)),
            0
        )
    )
)

end_time_second = z3.If(second == 0, end_E, z3.If(second == 1, end_J, end_M))
arrival_time_third = end_time_second + travel_time_step3

# Add constraints for third friend
s.add(z3.Implies(third == 0, start_E >= z3.If(arrival_time_third >= earliest[0], arrival_time_third, earliest[0])))
s.add(z3.Implies(third == 0, end_E == start_E + min_duration[0]))
s.add(z3.Implies(third == 0, end_E <= latest[0]))

s.add(z3.Implies(third == 1, start_J >= z3.If(arrival_time_third >= earliest[1], arrival_time_third, earliest[1])))
s.add(z3.Implies(third == 1, end_J == start_J + min_duration[1]))
s.add(z3.Implies(third == 1, end_J <= latest[1]))

s.add(z3.Implies(third == 2, start_M >= z3.If(arrival_time_third >= earliest[2], arrival_time_third, earliest[2])))
s.add(z3.Implies(third == 2, end_M == start_M + min_duration[2]))
s.add(z3.Implies(third == 2, end_M <= latest[2]))

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if s.check() == z3.sat:
    model = s.model()
    first_val = model[first].as_long()
    second_val = model[second].as_long()
    third_val = model[third].as_long()

    def get_start_end(friend_idx):
        if friend_idx == 0:
            return model[start_E].as_long(), model[end_E].as_long()
        elif friend_idx == 1:
            return model[start_J].as_long(), model[end_J].as_long()
        else:
            return model[start_M].as_long(), model[end_M].as_long()

    itinerary = []
    for order_idx in [first_val, second_val, third_val]:
        start, end = get_start_end(order_idx)
        if order_idx == 0:
            person = "Emily"
            location = "Presidio"
        elif order_idx == 1:
            person = "Joseph"
            location = "Richmond District"
        else:
            person = "Melissa"
            location = "Financial District"
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time_str(start),
            "end_time": minutes_to_time_str(end)
        })

    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")