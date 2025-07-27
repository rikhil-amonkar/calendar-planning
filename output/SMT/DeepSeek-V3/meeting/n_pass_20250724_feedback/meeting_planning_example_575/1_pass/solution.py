from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define travel times as a dictionary for easy lookup
    travel_times = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21,
    }

    # Define people and their constraints
    people = [
        {
            'name': 'Rebecca',
            'location': 'Presidio',
            'available_start': 18.25,  # 6:15 PM in 24-hour decimal
            'available_end': 20.75,   # 8:45 PM in 24-hour decimal
            'duration': 1.0           # 60 minutes
        },
        {
            'name': 'Linda',
            'location': 'Sunset District',
            'available_start': 15.5,  # 3:30 PM in 24-hour decimal
            'available_end': 19.75,    # 7:45 PM in 24-hour decimal
            'duration': 0.5           # 30 minutes
        },
        {
            'name': 'Elizabeth',
            'location': 'Haight-Ashbury',
            'available_start': 17.25,  # 5:15 PM in 24-hour decimal
            'available_end': 19.5,      # 7:30 PM in 24-hour decimal
            'duration': 1.75           # 105 minutes
        },
        {
            'name': 'William',
            'location': 'Mission District',
            'available_start': 13.25,  # 1:15 PM in 24-hour decimal
            'available_end': 19.5,     # 7:30 PM in 24-hour decimal
            'duration': 0.5            # 30 minutes
        },
        {
            'name': 'Robert',
            'location': 'Golden Gate Park',
            'available_start': 14.25,  # 2:15 PM in 24-hour decimal
            'available_end': 21.5,      # 9:30 PM in 24-hour decimal
            'duration': 0.75            # 45 minutes
        },
        {
            'name': 'Mark',
            'location': 'Russian Hill',
            'available_start': 10.0,    # 10:00 AM in 24-hour decimal
            'available_end': 21.25,    # 9:15 PM in 24-hour decimal
            'duration': 1.25            # 75 minutes
        }
    ]

    # Create variables for each person's start and end times
    for person in people:
        person['start'] = Real(f"start_{person['name']}")
        person['end'] = Real(f"end_{person['name']}")
        s.add(person['end'] == person['start'] + person['duration'])
        s.add(person['start'] >= person['available_start'])
        s.add(person['end'] <= person['available_end'])

    # Initial location is The Castro at 9:00 AM
    current_time = 9.0
    current_location = 'The Castro'

    # Order of meetings is not fixed, so we need to find a sequence that fits
    # We'll use a list to represent the order of meetings and enforce constraints
    # This is a simplified approach; a more complex model would use permutations
    # Here, we'll assume an order and let Z3 find the times

    # To simplify, we'll try to meet Mark first (since he's available earliest)
    # Then proceed to others, but Z3 will find the correct order

    # Enforce that all meetings are non-overlapping and account for travel times
    for i in range(len(people)):
        for j in range(len(people)):
            if i != j:
                # Either person i is before person j or vice versa
                before = Or(
                    people[i]['end'] + travel_times[(people[i]['location'], people[j]['location'])] <= people[j]['start'],
                    people[j]['end'] + travel_times[(people[j]['location'], people[i]['location'])] <= people[i]['start']
                )
                s.add(before)

    # Also ensure that the first meeting starts after travel from The Castro
    for person in people:
        s.add(person['start'] >= current_time + travel_times[(current_location, person['location'])])

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for person in people:
            start = model[person['start']].as_fraction()
            end = model[person['end']].as_fraction()
            # Convert fractions to float
            start_float = float(start.numerator) / float(start.denominator)
            end_float = float(end.numerator) / float(end.denominator)
            # Convert to HH:MM format
            start_hh = int(start_float)
            start_mm = int((start_float - start_hh) * 60)
            end_hh = int(end_float)
            end_mm = int((end_float - end_hh) * 60)
            start_time = f"{start_hh:02d}:{start_mm:02d}"
            end_time = f"{end_hh:02d}:{end_mm:02d}"
            itinerary.append({
                "action": "meet",
                "person": person['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))