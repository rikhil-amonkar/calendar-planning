import itertools
from z3 import *
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define travel times
    travel_times = {
        'Alamo Square': {
            'Russian Hill': 13,
            'Presidio': 18,
            'Chinatown': 16,
            'Sunset District': 16,
            'The Castro': 8,
            'Embarcadero': 17,
            'Golden Gate Park': 9,
        },
        'Russian Hill': {
            'Alamo Square': 15,
            'Presidio': 14,
            'Chinatown': 9,
            'Sunset District': 23,
            'The Castro': 21,
            'Embarcadero': 8,
            'Golden Gate Park': 21,
        },
        'Presidio': {
            'Alamo Square': 18,
            'Russian Hill': 14,
            'Chinatown': 21,
            'Sunset District': 15,
            'The Castro': 21,
            'Embarcadero': 20,
            'Golden Gate Park': 12,
        },
        'Chinatown': {
            'Alamo Square': 17,
            'Russian Hill': 7,
            'Presidio': 19,
            'Sunset District': 29,
            'The Castro': 22,
            'Embarcadero': 5,
            'Golden Gate Park': 23,
        },
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Presidio': 16,
            'Chinatown': 30,
            'The Castro': 17,
            'Embarcadero': 31,
            'Golden Gate Park': 11,
        },
        'The Castro': {
            'Alamo Square': 8,
            'Russian Hill': 18,
            'Presidio': 20,
            'Chinatown': 20,
            'Sunset District': 17,
            'Embarcadero': 22,
            'Golden Gate Park': 11,
        },
        'Embarcadero': {
            'Alamo Square': 19,
            'Russian Hill': 8,
            'Presidio': 20,
            'Chinatown': 7,
            'Sunset District': 30,
            'The Castro': 25,
            'Golden Gate Park': 25,
        },
        'Golden Gate Park': {
            'Alamo Square': 10,
            'Russian Hill': 19,
            'Presidio': 11,
            'Chinatown': 23,
            'Sunset District': 10,
            'The Castro': 13,
            'Embarcadero': 25,
        },
    }

    friends = [
        {
            'name': 'Emily',
            'location': 'Russian Hill',
            'available_start': 12 * 60 + 15,  # 735
            'available_end': 14 * 60 + 15,    # 855
            'required_duration': 105,
        },
        {
            'name': 'Mark',
            'location': 'Presidio',
            'available_start': 14 * 60 + 45,  # 905
            'available_end': 19 * 60 + 30,    # 1170
            'required_duration': 60,
        },
        {
            'name': 'Deborah',
            'location': 'Chinatown',
            'available_start': 7 * 60 + 30,   # 450
            'available_end': 15 * 60 + 30,    # 930
            'required_duration': 45,
        },
        {
            'name': 'Margaret',
            'location': 'Sunset District',
            'available_start': 21 * 60 + 30,  # 1290
            'available_end': 22 * 60 + 30,    # 1350
            'required_duration': 60,
        },
        {
            'name': 'George',
            'location': 'The Castro',
            'available_start': 7 * 60 + 30,   # 450
            'available_end': 14 * 60 + 15,    # 855
            'required_duration': 60,
        },
        {
            'name': 'Andrew',
            'location': 'Embarcadero',
            'available_start': 20 * 60 + 15,  # 1215
            'available_end': 22 * 60 + 0,     # 1320
            'required_duration': 75,
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available_start': 11 * 60 + 15,  # 675
            'available_end': 21 * 60 + 15,    # 1275
            'required_duration': 105,
        },
    ]

    # Try all subset sizes from largest to smallest
    for subset_size in range(len(friends), 0, -1):
        # Generate all combinations of friends of this size
        for subset in itertools.combinations(friends, subset_size):
            # Generate all permutations of this subset
            for perm in itertools.permutations(subset):
                # Create a Z3 solver
                solver = Solver()
                # Track previous location and current time
                prev_location = 'Alamo Square'
                current_time = 540  # 9:00 AM in minutes
                # Variables for start times
                start_vars = {}
                # For each friend in the permutation
                for friend in perm:
                    location = friend['location']
                    travel_time = travel_times[prev_location][location]
                    arrival_time = current_time + travel_time
                    start_var = Int(f'start_{friend["name"]}')
                    end_var = start_var + friend['required_duration']
                    # Add constraints
                    solver.add(start_var >= arrival_time)
                    solver.add(start_var >= friend['available_start'])
                    solver.add(end_var <= friend['available_end'])
                    # Save start_var for later retrieval
                    start_vars[friend['name']] = start_var
                    # Update for next iteration
                    prev_location = location
                    current_time = end_var
                # Check if the constraints are satisfiable
                if solver.check() == sat:
                    model = solver.model()
                    # Build the itinerary
                    itinerary = []
                    for friend in perm:
                        start_time = model[start_vars[friend['name']]]
                        end_time = start_time + friend['required_duration']
                        start_str = minutes_to_time_str(start_time.as_long())
                        end_str = minutes_to_time_str(end_time.as_long())
                        itinerary.append({
                            "action": "meet",
                            "person": friend['name'],
                            "start_time": start_str,
                            "end_time": end_str,
                        })
                    # Output the solution
                    print("SOLUTION:")
                    print(json.dumps({"itinerary": itinerary}))
                    return
    # If no solution found
    print("SOLUTION: No feasible schedule found.")

if __name__ == "__main__":
    main()