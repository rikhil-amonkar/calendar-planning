from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert availability windows to minutes since 9:00 AM
    # Sarah: 4:00 PM to 6:15 PM (16:00 to 18:15) -> 420 to 555 minutes
    sarah_available_start = 16 * 60 - 9 * 60  # 420 minutes
    sarah_available_end = 18 * 60 + 15 - 9 * 60  # 555 minutes

    # Jeffrey: 3:00 PM to 10:00 PM (15:00 to 22:00) -> 360 to 780 minutes
    jeffrey_available_start = 15 * 60 - 9 * 60  # 360 minutes
    jeffrey_available_end = 22 * 60 - 9 * 60  # 780 minutes

    # Brian: 4:00 PM to 5:30 PM (16:00 to 17:30) -> 420 to 510 minutes
    brian_available_start = 16 * 60 - 9 * 60  # 420 minutes
    brian_available_end = 17 * 60 + 30 - 9 * 60  # 510 minutes

    # Add constraints for each meeting's duration and availability
    s.add(sarah_start >= sarah_available_start)
    s.add(sarah_end <= sarah_available_end)
    s.add(sarah_end - sarah_start >= 60)  # 60 minutes with Sarah

    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end - jeffrey_start >= 75)  # 75 minutes with Jeffrey

    s.add(brian_start >= brian_available_start)
    s.add(brian_end <= brian_available_end)
    s.add(brian_end - brian_start >= 75)  # 75 minutes with Brian

    # Define locations for each person
    locations = {
        'sarah': 'North Beach',
        'jeffrey': 'Union Square',
        'brian': 'Alamo Square'
    }

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Alamo Square'): 16,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Alamo Square'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Union Square'): 14,
    }

    # We need to decide the order of meetings. Possible orders are permutations of sarah, jeffrey, brian.
    # We'll try all possible orders and find a feasible one.
    possible_orders = list(permutations(['sarah', 'jeffrey', 'brian']))

    feasible = False
    model = None

    for order in possible_orders:
        s.push()
        # Constraints for the order
        prev_location = 'Sunset District'
        prev_end = 0  # starting at 9:00 AM (0 minutes)

        for person in order:
            if person == 'sarah':
                current_start = sarah_start
                current_end = sarah_end
                current_location = 'North Beach'
            elif person == 'jeffrey':
                current_start = jeffrey_start
                current_end = jeffrey_end
                current_location = 'Union Square'
            elif person == 'brian':
                current_start = brian_start
                current_end = brian_end
                current_location = 'Alamo Square'
            
            # Travel time from previous location to current location
            travel_key = (prev_location, current_location)
            travel_time = travel_times[travel_key]
            
            s.add(current_start >= prev_end + travel_time)
            
            prev_end = current_end
            prev_location = current_location
        
        # Ensure no overlapping meetings
        if order == ('sarah', 'jeffrey', 'brian'):
            s.add(sarah_end <= jeffrey_start)
            s.add(jeffrey_end <= brian_start)
        elif order == ('sarah', 'brian', 'jeffrey'):
            s.add(sarah_end <= brian_start)
            s.add(brian_end <= jeffrey_start)
        elif order == ('jeffrey', 'sarah', 'brian'):
            s.add(jeffrey_end <= sarah_start)
            s.add(sarah_end <= brian_start)
        elif order == ('jeffrey', 'brian', 'sarah'):
            s.add(jeffrey_end <= brian_start)
            s.add(brian_end <= sarah_start)
        elif order == ('brian', 'sarah', 'jeffrey'):
            s.add(brian_end <= sarah_start)
            s.add(sarah_end <= jeffrey_start)
        elif order == ('brian', 'jeffrey', 'sarah'):
            s.add(brian_end <= jeffrey_start)
            s.add(jeffrey_end <= sarah_start)
        
        if s.check() == sat:
            feasible = True
            model = s.model()
            break
        s.pop()

    if not feasible:
        return {"itinerary": []}

    # Extract the meeting times from the model
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    itinerary = []
    for person in ['sarah', 'jeffrey', 'brian']:
        if person == 'sarah':
            start = model[sarah_start].as_long()
            end = model[sarah_end].as_long()
        elif person == 'jeffrey':
            start = model[jeffrey_start].as_long()
            end = model[jeffrey_end].as_long()
        elif person == 'brian':
            start = model[brian_start].as_long()
            end = model[brian_end].as_long()
        
        itinerary.append({
            "action": "meet",
            "person": person.capitalize(),
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])

    return {"itinerary": itinerary}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))