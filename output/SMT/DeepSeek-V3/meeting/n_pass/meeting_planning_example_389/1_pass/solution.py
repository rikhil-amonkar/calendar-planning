from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13,
    }

    # Define the friends and their constraints
    friends = [
        {
            'name': 'Sarah',
            'location': 'Fisherman\'s Wharf',
            'available_start': (14, 45),  # 2:45 PM
            'available_end': (17, 30),    # 5:30 PM
            'min_duration': 105,         # minutes
        },
        {
            'name': 'Mary',
            'location': 'Richmond District',
            'available_start': (13, 0),   # 1:00 PM
            'available_end': (19, 15),    # 7:15 PM
            'min_duration': 75,          # minutes
        },
        {
            'name': 'Helen',
            'location': 'Mission District',
            'available_start': (21, 45),  # 9:45 PM
            'available_end': (22, 30),    # 10:30 PM
            'min_duration': 30,           # minutes
        },
        {
            'name': 'Thomas',
            'location': 'Bayview',
            'available_start': (15, 15),  # 3:15 PM
            'available_end': (18, 45),    # 6:45 PM
            'min_duration': 120,          # minutes
        }
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        name = friend['name']
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = (start, end)
        # Constrain the meeting to be within the friend's availability
        s.add(start >= time_to_minutes(*friend['available_start']))
        s.add(end <= time_to_minutes(*friend['available_end']))
        # Constrain the meeting duration
        s.add(end - start >= friend['min_duration'])

    # Constrain the order of meetings and travel times
    # We'll assume the order is: Mary -> Sarah -> Thomas -> Helen
    # This is a heuristic; in a more general solution, we'd explore all permutations
    mary_start, mary_end = meeting_vars['Mary']
    sarah_start, sarah_end = meeting_vars['Sarah']
    thomas_start, thomas_end = meeting_vars['Thomas']
    helen_start, helen_end = meeting_vars['Helen']

    # Starting at Haight-Ashbury at 9:00 AM (0 minutes)
    # First travel to Mary in Richmond District: 10 minutes
    s.add(mary_start >= 10)
    # Travel from Mary to Sarah: Richmond District to Fisherman's Wharf: 18 minutes
    s.add(sarah_start >= mary_end + 18)
    # Travel from Sarah to Thomas: Fisherman's Wharf to Bayview: 26 minutes
    s.add(thomas_start >= sarah_end + 26)
    # Travel from Thomas to Helen: Bayview to Mission District: 13 minutes
    s.add(helen_start >= thomas_end + 13)

    # Check if all meetings can fit
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend['name']
            start, end = meeting_vars[name]
            start_time = model.eval(start).as_long()
            end_time = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))