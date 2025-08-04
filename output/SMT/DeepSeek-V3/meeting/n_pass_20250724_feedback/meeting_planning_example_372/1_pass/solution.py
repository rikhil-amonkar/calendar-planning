from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Mission District'): 24,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Mission District'): 10,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Mission District'): 16,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
    }

    # Friends' availability and meeting constraints
    friends = {
        'Charles': {
            'location': 'Alamo Square',
            'start': 18 * 60,  # 6:00 PM in minutes
            'end': 20 * 60 + 45,  # 8:45 PM in minutes
            'min_duration': 90,
        },
        'Margaret': {
            'location': 'Russian Hill',
            'start': 9 * 60,  # 9:00 AM in minutes
            'end': 16 * 60,  # 4:00 PM in minutes
            'min_duration': 30,
        },
        'Daniel': {
            'location': 'Golden Gate Park',
            'start': 8 * 60,  # 8:00 AM in minutes
            'end': 13 * 60 + 30,  # 1:30 PM in minutes
            'min_duration': 15,
        },
        'Stephanie': {
            'location': 'Mission District',
            'start': 20 * 60 + 30,  # 8:30 PM in minutes
            'end': 22 * 60,  # 10:00 PM in minutes
            'min_duration': 90,
        }
    }

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Sunset District'

    # Variables for each meeting
    meet_vars = {}
    for name in friends:
        meet_start = Int(f'meet_{name}_start')
        meet_end = Int(f'meet_{name}_end')
        meet_vars[name] = (meet_start, meet_end)

    # Constraints for each meeting
    for name in friends:
        friend = friends[name]
        meet_start, meet_end = meet_vars[name]
        s.add(meet_start >= friend['start'])
        s.add(meet_end <= friend['end'])
        s.add(meet_end - meet_start >= friend['min_duration'])

    # Meeting order and travel time constraints
    # We need to decide the order of meetings. Let's assume the order is Margaret, Daniel, Charles, Stephanie.
    # This is a heuristic; in a more complex scenario, we'd need to explore permutations.
    # For simplicity, we'll proceed with this order and check feasibility.

    # Margaret (Russian Hill)
    margaret_start, margaret_end = meet_vars['Margaret']
    travel_to_margaret = travel_times[(current_location, 'Russian Hill')]
    s.add(margaret_start >= current_time + travel_to_margaret)

    # Daniel (Golden Gate Park)
    daniel_start, daniel_end = meet_vars['Daniel']
    travel_to_daniel = travel_times[('Russian Hill', 'Golden Gate Park')]
    s.add(daniel_start >= margaret_end + travel_to_daniel)

    # Charles (Alamo Square)
    charles_start, charles_end = meet_vars['Charles']
    travel_to_charles = travel_times[('Golden Gate Park', 'Alamo Square')]
    s.add(charles_start >= daniel_end + travel_to_charles)

    # Stephanie (Mission District)
    stephanie_start, stephanie_end = meet_vars['Stephanie']
    travel_to_stephanie = travel_times[('Alamo Square', 'Mission District')]
    s.add(stephanie_start >= charles_end + travel_to_stephanie)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []

        for name in ['Margaret', 'Daniel', 'Charles', 'Stephanie']:
            start = model.evaluate(meet_vars[name][0]).as_long()
            end = model.evaluate(meet_vars[name][1]).as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))