from z3 import *

# Define the travel times
travel_times = {
    'North Beach to Pacific Heights': 8,
    'North Beach to Embarcadero': 6,
    'Pacific Heights to North Beach': 9,
    'Pacific Heights to Embarcadero': 10,
    'Embarcadero to North Beach': 5,
    'Embarcadero to Pacific Heights': 11
}

# Define the constraints
arrive_time = 9 * 60  # 9:00 AM in minutes
karen_start = 6 * 60 + 45  # 6:45 PM in minutes
karen_end = 20 * 60 + 15  # 8:15 PM in minutes
mark_start = 13 * 60  # 1:00 PM in minutes
mark_end = 17 * 60 + 45  # 5:45 PM in minutes
min_time_with_karen = 90  # 90 minutes
min_time_with_mark = 120  # 120 minutes

# Define the variables
visit_pacific_heights = Bool('visit_pacific_heights')
visit_embarcadero = Bool('visit_embarcadero')
leave_time = Int('leave_time')
visit_time_with_karen = Int('visit_time_with_karen')
visit_time_with_mark = Int('visit_time_with_mark')

# Define the constraints
s = Optimize()
s.add(leave_time >= arrive_time)
s.add(visit_time_with_karen >= karen_start)
s.add(visit_time_with_karen <= karen_end)
s.add(visit_time_with_mark >= mark_start)
s.add(visit_time_with_mark <= mark_end)
s.add(visit_time_with_karen >= leave_time + min_time_with_karen)
s.add(visit_time_with_mark >= leave_time + min_time_with_mark)
if visit_pacific_heights:
    s.add(visit_time_with_karen <= (leave_time + travel_times['North Beach to Pacific Heights'] + travel_times['Pacific Heights to North Beach']))
if visit_embarcadero:
    s.add(visit_time_with_mark <= (leave_time + travel_times['North Beach to Embarcadero'] + travel_times['Embarcadero to North Beach']))

# Define the objective function
s.minimize((leave_time + travel_times['North Beach to Pacific Heights'] + travel_times['Pacific Heights to North Beach'] if visit_pacific_heights else 0) +
           (leave_time + travel_times['North Beach to Embarcadero'] + travel_times['Embarcadero to North Beach'] if visit_embarcadero else 0))

# Solve the optimization problem
solution = s.check()

# Print the solution
if solution == sat:
    m = s.model()
    print("Visit Pacific Heights:", m[visit_pacific_heights])
    print("Visit Embarcadero:", m[visit_embarcadero])
    print("Leave Time:", m[leave_time])
    print("Visit Time with Karen:", m[visit_time_with_karen])
    print("Visit Time with Mark:", m[visit_time_with_mark])
else:
    print("No solution found")