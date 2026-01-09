import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Union Square': {
            'Mission District': 14, 'Fisherman\'s Wharf': 15, 'Russian Hill': 13,
            'Marina District': 18, 'North Beach': 10, 'Chinatown': 7,
            'Pacific Heights': 15, 'The Castro': 17, 'Nob Hill': 9, 'Sunset District': 27
        },
        'Mission District': {
            'Union Square': 15, 'Fisherman\'s Wharf': 22, 'Russian Hill': 15,
            'Marina District': 19, 'North Beach': 17, 'Chinatown': 16,
            'Pacific Heights': 16, 'The Castro': 7, 'Nob Hill': 12, 'Sunset District': 24
        },
        'Fisherman\'s Wharf': {
            'Union Square': 13, 'Mission District': 22, 'Russian Hill': 7,
            'Marina District': 9, 'North Beach': 6, 'Chinatown': 12,
            'Pacific Heights': 12, 'The Castro': 27, 'Nob Hill': 11, 'Sunset District': 27
        },
        'Russian Hill': {
            'Union Square': 10, 'Mission District': 16, 'Fisherman\'s Wharf': 7,
            'Marina District': 7, 'North Beach': 5, 'Chinatown': 9,
            'Pacific Heights': 7, 'The Castro': 21, 'Nob Hill': 5, 'Sunset District': 23
        },
        'Marina District': {
            'Union Square': 16, 'Mission District': 20, 'Fisherman\'s Wharf': 10,
            'Russian Hill': 8, 'North Beach': 11, 'Chinatown': 15,
            'Pacific Heights': 7, 'The Castro': 22, 'Nob Hill': 12, 'Sunset District': 19
        },
        'North Beach': {
            'Union Square': 7, 'Mission District': 18, 'Fisherman\'s Wharf': 5,
            'Russian Hill': 4, 'Marina District': 9, 'Chinatown': 6,
            'Pacific Heights': 8, 'The Castro': 23, 'Nob Hill': 7, 'Sunset District': 27
        },
        'Chinatown': {
            'Union Square': 7, 'Mission District': 17, 'Fisherman\'s Wharf': 8,
            'Russian Hill': 7, 'Marina District': 12, 'North Beach': 3,
            'Pacific Heights': 10, 'The Castro': 22, 'Nob Hill': 9, 'Sunset District': 29
        },
        'Pacific Heights': {
            'Union Square': 12, 'Mission District': 15, 'Fisherman\'s Wharf': 13,
            'Russian Hill': 7, 'Marina District': 6, 'North Beach': 9,
            'Chinatown': 11, 'The Castro': 16, 'Nob Hill': 8, 'Sunset District': 21
        },
        'The Castro': {
            'Union Square': 19, 'Mission District': 7, 'Fisherman\'s Wharf': 24,
            'Russian Hill': 18, 'Marina District': 21, 'North Beach': 20,
            'Chinatown': 22, 'Pacific Heights': 16, 'Nob Hill': 16, 'Sunset District': 17
        },
        'Nob Hill': {
            'Union Square': 7, 'Mission District': 13, 'Fisherman\'s Wharf': 10,
            'Russian Hill': 5, 'Marina District': 11, 'North Beach': 8,
            'Chinatown': 6, 'Pacific Heights': 8, 'The Castro': 17, 'Sunset District': 24
        },
        'Sunset District': {
            'Union Square': 30, 'Mission District': 25, 'Fisherman\'s Wharf': 29,
            'Russian Hill': 24, 'Marina District': 21, 'North Beach': 28,
            'Chinatown': 30, 'Pacific Heights': 21, 'The Castro': 17, 'Nob Hill': 27
        }
    }

    # Define friends with their constraints
    friends = [
        {'name': 'Kevin', 'location': 'Mission District', 'start': 20.75, 'end': 21.75, 'duration': 60},
        {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'start': 17.25, 'end': 20.0, 'duration': 90},
        {'name': 'Jessica', 'location': 'Russian Hill', 'start': 9.0, 'end': 15.0, 'duration': 120},
        {'name': 'Jason', 'location': 'Marina District', 'start': 15.25, 'end': 21.75, 'duration': 120},
        {'name': 'John', 'location': 'North Beach', 'start': 9.75, 'end': 18.0, 'duration': 15},
        {'name': 'Karen', 'location': 'Chinatown', 'start': 16.75, 'end': 19.0, 'duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 17.5, 'end': 18.25, 'duration': 45},
        {'name': 'Amanda', 'location': 'The Castro', 'start': 20.0, 'end': 21.25, 'duration': 60},
        {'name': 'Nancy', 'location': 'Nob Hill', 'start': 9.75, 'end': 13.0, 'duration': 45},
        {'name': 'Rebecca', 'location': 'Sunset District', 'start': 8.75, 'end': 15.0, 'duration': 75}
    ]

    # Start location and time
    current_location = 'Union Square'
    current_time = 9.0  # 9:00 AM

    # Create problem instance
    problem = Problem()

    # Add variables for each friend (0 = not visited, 1 = visited)
    for friend in friends:
        problem.addVariable(friend['name'], [0, 1])

    # Add constraint to maximize number of friends met
    def maximize_friends(*args):
        return sum(args)

    problem.addConstraint(maximize_friends, [friend['name'] for friend in friends])

    # Solve the problem
    solutions = problem.getSolutions()

    # Find the solution with maximum friends
    max_friends_solution = max(solutions, key=lambda x: sum(x.values()))

    # Build itinerary based on the solution
    itinerary = []
    current_location = 'Union Square'
    current_time = 9.0

    # Filter friends that are included in the solution
    selected_friends = [friend for friend in friends if max_friends_solution[friend['name']] == 1]

    # Sort friends by their availability start time for a logical order
    selected_friends.sort(key=lambda x: x['start'])

    for friend in selected_friends:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']] / 60.0
        
        # Calculate arrival time
        arrival_time = current_time + travel_time
        
        # Check if we can meet within friend's availability
        if arrival_time <= friend['end']:
            # Calculate meeting start time (max of arrival time and friend's start time)
            meeting_start = max(arrival_time, friend['start'])
            
            # Calculate meeting end time
            meeting_end = meeting_start + (friend['duration'] / 60.0)
            
            # Check if meeting fits within friend's availability
            if meeting_end <= friend['end']:
                # Add to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': format_time(meeting_start),
                    'end_time': format_time(meeting_end)
                })
                
                # Update current location and time
                current_location = friend['location']
                current_time = meeting_end

    # Output result as JSON
    result = {
        'itinerary': itinerary
    }
    
    print(json.dumps(result, indent=2))

def format_time(time_float):
    """Convert float time (e.g., 9.5) to string format (e.g., '9:30')"""
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()