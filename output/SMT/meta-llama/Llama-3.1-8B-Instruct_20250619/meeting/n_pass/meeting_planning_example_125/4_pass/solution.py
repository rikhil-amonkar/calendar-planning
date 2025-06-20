from z3 import *

# Define the variables
start_time = 0  # Start time of the day (in minutes)
end_time = 12 * 60  # End time of the day (in minutes)
stephanie_arrive, stephanie_leave = 8 * 60 + 15, 11 * 60 + 30  # Stephanie's arrival and departure times
john_arrive, john_leave = 10 * 60 + 15, 20 * 60 + 45  # John's arrival and departure times
min_stephanie_meet, min_john_meet = 90, 30  # Minimum meeting time for Stephanie and John
travel_time_embarcadero_financial_district, travel_time_embarcadero_alamo_square = 5, 19  # Travel times
travel_time_financial_district_embarcadero, travel_time_financial_district_alamo_square = 4, 17  # Travel times
travel_time_alamo_square_embarcadero, travel_time_alamo_square_financial_district = 17, 17  # Travel times

# Define the decision variables
x_stephanie = Int('x_stephanie')  # Time to meet Stephanie
x_john = Int('x_john')  # Time to meet John
x_meet_stephanie = Bool('meet_stephanie')  # Whether to meet Stephanie
x_meet_john = Bool('meet_john')  # Whether to meet John

# Define the constraints
s = Optimize()
s.add(x_stephanie >= stephanie_arrive)
s.add(x_stephanie <= stephanie_leave - min_stephanie_meet)
s.add(x_john >= john_arrive)
s.add(x_john <= john_leave - min_john_meet)
s.add(Implies(x_meet_stephanie, x_stephanie >= stephanie_arrive))
s.add(Implies(x_meet_stephanie, x_stephanie <= stephanie_leave - min_stephanie_meet))
s.add(Implies(x_meet_john, x_john >= john_arrive))
s.add(Implies(x_meet_john, x_john <= john_leave - min_john_meet))
s.add(x_meet_stephanie + x_meet_john == 1)  # Exactly one meeting
s.add(x_meet_stephanie + x_meet_john >= 1)  # At least one meeting
s.add(x_meet_stephanie + x_meet_john <= 2)  # At most one meeting
s.add(x_stephanie + x_john >= 0)  # Non-negative travel time
s.add(x_stephanie + x_john + travel_time_embarcadero_financial_district + travel_time_financial_district_embarcadero + travel_time_alamo_square_embarcadero + travel_time_embarcadero_alamo_square <= end_time)

# Solve the optimization problem
s.minimize(x_stephanie + x_john + travel_time_embarcadero_financial_district + travel_time_financial_district_embarcadero + travel_time_alamo_square_embarcadero + travel_time_embarcadero_alamo_square)
result = s.check()

# Print the solution
if result == sat:
    model = s.model()
    print("SOLUTION:")
    if model[x_meet_stephanie]:
        print(f"Meet Stephanie at {model[x_stephanie].as_long() / 60} hours")
    if model[x_meet_john]:
        print(f"Meet John at {(model[x_john].as_long() + travel_time_embarcadero_alamo_square) / 60} hours")
    print(f"Total travel time: {(model[x_stephanie].as_long() + model[x_john].as_long() + travel_time_embarcadero_financial_district + travel_time_financial_district_embarcadero + travel_time_alamo_square_embarcadero + travel_time_embarcadero_alamo_square) / 60} hours")
else:
    print("No solution found.")