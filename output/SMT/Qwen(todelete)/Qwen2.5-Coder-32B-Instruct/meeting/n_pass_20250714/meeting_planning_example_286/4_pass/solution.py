from z3 import *

# Define the time points in minutes from 9:00 AM
nine_am = 0
eleven_thirty_am = 150
one_twenty_five_pm = 745  # 12:45 PM + 120 minutes
three_pm = 180
three_fifteen_pm = 210
eight_fifteen_pm = 495   # 8:15 PM - 9:00 AM
ten_fifteen_am = 65      # 10:15 AM - 9:00 AM
eleven_forty_five_am = 105  # 11:45 AM - 9:00 AM

# Create a solver instance
solver = Solver()

# Define variables for the start times of meeting each friend
start_rebecca = Int('start_rebecca')
end_rebecca = Int('end_rebecca')
start_karen = Int('start_karen')
end_karen = Int('end_karen')
start_carol = Int('start_carol')
end_carol = Int('end_carol')

# Add constraints for the minimum meeting durations
solver.add(end_rebecca - start_rebecca >= 120)
solver.add(end_karen - start_karen >= 120)
solver.add(end_carol - start_carol >= 30)

# Add constraints for the availability of each friend
solver.add(start_rebecca >= eleven_thirty_am)
solver.add(end_rebecca <= eight_fifteen_pm)
solver.add(start_karen >= one_twenty_five_pm)
solver.add(end_karen <= three_pm)
solver.add(start_carol >= ten_fifteen_am)
solver.add(end_carol <= eleven_forty_five_am)

# Define travel times
travel_times = {
    ('union_square', 'mission_district'): 14,
    ('union_square', 'bayview'): 15,
    ('union_square', 'sunset_district'): 26,
    ('mission_district', 'union_square'): 15,
    ('mission_district', 'bayview'): 15,
    ('mission_district', 'sunset_district'): 24,
    ('bayview', 'union_square'): 17,
    ('bayview', 'mission_district'): 13,
    ('bayview', 'sunset_district'): 23,
    ('sunset_district', 'union_square'): 30,
    ('sunset_district', 'mission_district'): 24,
    ('sunset_district', 'bayview'): 22
}

# Define variables for the location changes
locations = ['union_square', 'mission_district', 'bayview', 'sunset_district']
location_vars = [String(f'location_{i}') for i in range(4)]  # We need 4 slots: start, between meetings, end

# Initial location is Union Square
solver.add(location_vars[0] == 'union_square')

# Constraints for traveling between locations and meeting times
# Meeting Carol first
solver.add(location_vars[1] == 'mission_district')
solver.add(start_carol == nine_am)
solver.add(end_carol == start_rebecca - travel_times[('union_square', 'mission_district')])

# Meeting Rebecca next
solver.add(location_vars[2] == 'bayview')
solver.add(start_rebecca >= eleven_thirty_am)
solver.add(end_rebecca <= eight_fifteen_pm)
solver.add(end_rebecca - start_rebecca >= 120)
solver.add(start_karen >= end_rebecca + travel_times[('mission_district', 'bayview')])

# Meeting Karen last
solver.add(location_vars[3] == 'bayview')
solver.add(start_karen >= one_twenty_five_pm)
solver.add(end_karen <= three_pm)
solver.add(end_karen - start_karen >= 120)
solver.add(end_karen <= end_rebecca + travel_times[('bayview', 'bayview')])

# Ensure that exactly three people are met
solver.add(And(
    Or(start_carol >= nine_am, end_carol <= eleven_forty_five_am),
    Or(start_rebecca >= eleven_thirty_am, end_rebecca <= eight_fifteen_pm),
    Or(start_karen >= one_twenty_five_pm, end_karen <= three_pm)
))

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Start meeting Carol at: {model[start_carol]} minutes past 9:00 AM")
    print(f"End meeting Carol at: {model[end_carol]} minutes past 9:00 AM")
    print(f"Start meeting Rebecca at: {model[start_rebecca]} minutes past 9:00 AM")
    print(f"End meeting Rebecca at: {model[end_rebecca]} minutes past 9:00 AM")
    print(f"Start meeting Karen at: {model[start_karen]} minutes past 9:00 AM")
    print(f"End meeting Karen at: {model[end_karen]} minutes past 9:00 AM")
    print(f"Locations visited: {[model[l].as_string() for l in location_vars]}")
else:
    print("No solution found.")