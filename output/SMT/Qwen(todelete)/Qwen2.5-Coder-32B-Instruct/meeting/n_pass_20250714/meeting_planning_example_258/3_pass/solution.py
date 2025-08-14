from z3 import *

# Define the variables for the start time of meeting each friend
betty_start = Int('betty_start')
david_start = Int('david_start')
barbara_start = Int('barbara_start')

# Define the solver
solver = Solver()

# Constraints for Betty's availability and meeting duration
solver.add(betty_start >= 615)  # 10:15 AM in minutes since 9:00 AM
solver.add(betty_start + 45 <= 570)  # 9:30 PM in minutes since 9:00 AM

# Constraints for David's availability and meeting duration
solver.add(david_start >= 900)  # 1:00 PM in minutes since 9:00 AM
solver.add(david_start + 90 <= 525)  # 8:15 PM in minutes since 9:00 AM

# Constraints for Barbara's availability and meeting duration
solver.add(barbara_start >= 90)  # 9:15 AM in minutes since 9:00 AM
solver.add(barbara_start + 120 <= 525)  # 8:15 PM in minutes since 9:00 AM

# Travel times in minutes
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define binary variables to indicate whether we meet each friend
meet_betty = Bool('meet_betty')
meet_david = Bool('meet_david')
meet_barbara = Bool('meet_barbara')

# Constraints to ensure we meet exactly 3 people
solver.add(meet_betty + meet_david + meet_barbara == 3)

# Constraints for meeting Betty
solver.add(Implies(meet_betty, betty_start >= travel_times[('Embarcadero', 'Presidio')]))
solver.add(Implies(meet_betty, betty_start + 45 <= 570))

# Constraints for meeting David
solver.add(Implies(meet_david, david_start >= betty_start + travel_times[('Presidio', 'Richmond District')] + 45))
solver.add(Implies(meet_david, david_start + 90 <= 525))

# Constraints for meeting Barbara
# Ensure Barbara's meeting time is within her availability
solver.add(Implies(meet_barbara, barbara_start >= travel_times[('Embarcadero', 'Fisherman\'s Wharf')]))
solver.add(Implies(meet_barbara, barbara_start + 120 <= 525))

# Ensure Barbara's meeting does not conflict with other meetings
solver.add(Implies(And(meet_betty, meet_barbara), barbara_start >= betty_start + travel_times[('Presidio', 'Fisherman\'s Wharf')] + 45))
solver.add(Implies(And(meet_david, meet_barbara), barbara_start >= david_start + travel_times[('Richmond District', 'Fisherman\'s Wharf')] + 90))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    betty_meeting_start = model[betty_start].as_long() if model[meet_betty] else None
    david_meeting_start = model[david_start].as_long() if model[meet_david] else None
    barbara_meeting_start = model[barbara_start].as_long() if model[meet_barbara] else None
    
    def convert_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        am_pm = "AM" if hours < 12 else "PM"
        hours = hours % 12 if hours != 0 else 12
        return f"{hours:02}:{minutes:02}{am_pm}"
    
    SOLUTION = ""
    if betty_meeting_start is not None:
        SOLUTION += f"Meeting Betty from {convert_to_time(betty_meeting_start)} to {convert_to_time(betty_meeting_start + 45)}\n"
    if david_meeting_start is not None:
        SOLUTION += f"Meeting David from {convert_to_time(david_meeting_start)} to {convert_to_time(david_meeting_start + 90)}\n"
    if barbara_meeting_start is not None:
        SOLUTION += f"Meeting Barbara from {convert_to_time(barbara_meeting_start)} to {convert_to_time(barbara_meeting_start + 120)}\n"
else:
    SOLUTION = "No feasible schedule found."

print(SOLUTION)