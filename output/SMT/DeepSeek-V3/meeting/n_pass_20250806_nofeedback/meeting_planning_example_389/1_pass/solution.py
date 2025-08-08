from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables for each meeting
    # Sarah at Fisherman's Wharf: 2:45PM to 5:30PM, min 105 minutes (1.75 hours)
    sarah_start = Real('sarah_start')
    sarah_end = Real('sarah_end')
    s.add(sarah_start >= 14.75)  # 2:45PM is 14.75 in 24-hour format
    s.add(sarah_end <= 17.5)     # 5:30PM is 17.5
    s.add(sarah_end - sarah_start >= 1.75)  # 105 minutes is 1.75 hours

    # Mary at Richmond District: 1:00PM to 7:15PM, min 75 minutes (1.25 hours)
    mary_start = Real('mary_start')
    mary_end = Real('mary_end')
    s.add(mary_start >= 13.0)    # 1:00PM is 13.0
    s.add(mary_end <= 19.25)     # 7:15PM is 19.25
    s.add(mary_end - mary_start >= 1.25)

    # Helen at Mission District: 9:45PM to 10:30PM, min 30 minutes (0.5 hours)
    helen_start = Real('helen_start')
    helen_end = Real('helen_end')
    s.add(helen_start >= 21.75)  # 9:45PM is 21.75
    s.add(helen_end <= 22.5)     # 10:30PM is 22.5
    s.add(helen_end - helen_start >= 0.5)

    # Thomas at Bayview: 3:15PM to 6:45PM, min 120 minutes (2 hours)
    thomas_start = Real('thomas_start')
    thomas_end = Real('thomas_end')
    s.add(thomas_start >= 15.25)  # 3:15PM is 15.25
    s.add(thomas_end <= 18.75)    # 6:45PM is 18.75
    s.add(thomas_end - thomas_start >= 2.0)

    # Travel times (in hours)
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23/60,
        ('Haight-Ashbury', 'Richmond District'): 10/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22/60,
        ('Fisherman\'s Wharf', 'Richmond District'): 18/60,
        ('Fisherman\'s Wharf', 'Mission District'): 22/60,
        ('Fisherman\'s Wharf', 'Bayview'): 26/60,
        ('Richmond District', 'Haight-Ashbury'): 10/60,
        ('Richmond District', 'Fisherman\'s Wharf'): 18/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Bayview'): 26/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Fisherman\'s Wharf'): 22/60,
        ('Mission District', 'Richmond District'): 20/60,
        ('Mission District', 'Bayview'): 15/60,
        ('Bayview', 'Haight-Ashbury'): 19/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Bayview', 'Richmond District'): 25/60,
        ('Bayview', 'Mission District'): 13/60,
    }

    # Define the order of meetings (we'll try to meet all friends)
    # Possible order: Mary -> Sarah -> Thomas -> Helen
    # Start at Haight-Ashbury at 9:00AM (9.0)
    # First meeting: Mary at Richmond District
    s.add(mary_start >= 9.0 + travel_times[('Haight-Ashbury', 'Richmond District')])

    # After Mary, go to Sarah at Fisherman's Wharf
    s.add(sarah_start >= mary_end + travel_times[('Richmond District', 'Fisherman\'s Wharf')])

    # After Sarah, go to Thomas at Bayview
    s.add(thomas_start >= sarah_end + travel_times[('Fisherman\'s Wharf', 'Bayview')])

    # After Thomas, go to Helen at Mission District
    s.add(helen_start >= thomas_end + travel_times[('Bayview', 'Mission District')])

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        # Extract times from the model
        sarah_start_val = model[sarah_start].as_fraction()
        sarah_end_val = model[sarah_end].as_fraction()
        mary_start_val = model[mary_start].as_fraction()
        mary_end_val = model[mary_end].as_fraction()
        helen_start_val = model[helen_start].as_fraction()
        helen_end_val = model[helen_end].as_fraction()
        thomas_start_val = model[thomas_start].as_fraction()
        thomas_end_val = model[thomas_end].as_fraction()

        # Convert fractional hours to HH:MM format
        def to_hhmm(fraction):
            hours = fraction.numerator // fraction.denominator
            minutes = (fraction.numerator % fraction.denominator) * 60 // fraction.denominator
            return f"{hours:02d}:{minutes:02d}"

        itinerary = [
            {"action": "meet", "person": "Mary", "start_time": to_hhmm(mary_start_val), "end_time": to_hhmm(mary_end_val)},
            {"action": "meet", "person": "Sarah", "start_time": to_hhmm(sarah_start_val), "end_time": to_hhmm(sarah_end_val)},
            {"action": "meet", "person": "Thomas", "start_time": to_hhmm(thomas_start_val), "end_time": to_hhmm(thomas_end_val)},
            {"action": "meet", "person": "Helen", "start_time": to_hhmm(helen_start_val), "end_time": to_hhmm(helen_end_val)},
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))