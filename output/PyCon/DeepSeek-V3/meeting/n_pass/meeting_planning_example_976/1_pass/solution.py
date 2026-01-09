import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Marina District'): 12,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Marina District'): 12,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Marina District'): 11,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'The Castro'): 27,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Fisherman\'s Wharf'): 10
    }

    # Friend constraints
    friends = [
        {'name': 'Matthew', 'location': 'Bayview', 'start': '19:15', 'end': '22:00', 'min_duration': 120},
        {'name': 'Karen', 'location': 'Chinatown', 'start': '19:15', 'end': '21:15', 'min_duration': 90},
        {'name': 'Sarah', 'location': 'Alamo Square', 'start': '20:00', 'end': '21:45', 'min_duration': 105},
        {'name': 'Jessica', 'location': 'Nob Hill', 'start': '16:30', 'end': '18:45', 'min_duration': 120},
        {'name': 'Stephanie', 'location': 'Presidio', 'start': '7:30', 'end': '10:15', 'min_duration': 60},
        {'name': 'Mary', 'location': 'Union Square', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
        {'name': 'Charles', 'location': 'The Castro', 'start': '16:30', 'end': '22:00', 'min_duration': 105},
        {'name': 'Nancy', 'location': 'North Beach', 'start': '14:45', 'end': '20:00', 'min_duration': 15},
        {'name': 'Thomas', 'location': 'Fisherman\'s Wharf', 'start': '13:30', 'end': '19:00', 'min_duration': 30},
        {'name': 'Brian', 'location': 'Marina District', 'start': '12:15', 'end': '18:00', 'min_duration': 60}
    ]

    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, '%H:%M')
        base_time = datetime.strptime('9:00', '%H:%M')
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)

    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime('9:00', '%H:%M')
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime('%H:%M').lstrip('0')

    # Create problem
    problem = constraint.Problem()

    # Variables: start time and duration for each friend
    for i, friend in enumerate(friends):
        friend_start_min = time_to_minutes(friend['start'])
        friend_end_min = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']
        
        # Start time can be from friend's start time to (end time - min duration)
        problem.addVariable(f'start_{i}', range(friend_start_min, friend_end_min - min_duration + 1))
        # Duration must be at least the minimum
        problem.addVariable(f'duration_{i}', range(min_duration, friend_end_min - friend_start_min + 1))

    # Add constraints for travel time between consecutive meetings
    def travel_constraint(*args):
        # Extract all start times and durations
        starts = [args[i] for i in range(0, len(args), 2)]
        durations = [args[i] for i in range(1, len(args), 2)]
        
        # Calculate end times
        ends = [starts[i] + durations[i] for i in range(len(starts))]
        
        # Create list of meetings with start, end, and location
        meetings = []
        for i in range(len(friends)):
            meetings.append({
                'start': starts[i],
                'end': ends[i],
                'location': friends[i]['location']
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Check travel time constraints between consecutive meetings
        for j in range(len(meetings) - 1):
            current_meeting = meetings[j]
            next_meeting = meetings[j + 1]
            
            # If meetings overlap, it's invalid
            if current_meeting['end'] > next_meeting['start']:
                return False
            
            # Calculate required travel time
            travel_key = (current_meeting['location'], next_meeting['location'])
            if travel_key in travel_times:
                required_travel = travel_times[travel_key]
            else:
                # If no direct travel time, estimate conservatively
                return False
            
            # Check if there's enough time to travel
            if next_meeting['start'] - current_meeting['end'] < required_travel:
                return False
        
        return True

    # Add the travel constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.append(f'start_{i}')
        all_vars.append(f'duration_{i}')
    
    problem.addConstraint(travel_constraint, all_vars)

    # Find solution that maximizes total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        best_meetings = 0
        
        for sol in problem.getSolutions():
            meetings_count = sum(1 for i in range(len(friends)) if sol[f'duration_{i}'] >= friends[i]['min_duration'])
            if meetings_count > best_meetings:
                best_meetings = meetings_count
                best_solution = sol
        
        if best_solution is None:
            # If still no solution, create a minimal schedule
            itinerary = []
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
            
        solution = best_solution
    else:
        # Find solution with maximum total meeting time
        max_duration = -1
        best_solution = None
        
        for sol in solutions:
            total_duration = sum(sol[f'duration_{i}'] for i in range(len(friends)))
            if total_duration > max_duration:
                max_duration = total_duration
                best_solution = sol
        
        solution = best_solution

    # Build itinerary
    itinerary = []
    for i in range(len(friends)):
        if f'start_{i}' in solution:
            start_time = minutes_to_time(solution[f'start_{i}'])
            end_time = minutes_to_time(solution[f'start_{i}'] + solution[f'duration_{i}'])
            
            itinerary.append({
                "action": "meet",
                "location": friends[i]['location'],
                "person": friends[i]['name'],
                "start_time": start_time,
                "end_time": end_time
            })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()