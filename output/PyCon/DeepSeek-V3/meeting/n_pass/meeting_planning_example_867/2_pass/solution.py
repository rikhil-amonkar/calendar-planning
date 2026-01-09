from constraint import Problem, AllDifferentConstraint
import json
from itertools import permutations

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Haight-Ashbury': {
            'Mission District': 11, 'Union Square': 19, 'Pacific Heights': 12, 
            'Bayview': 18, 'Fisherman\'s Wharf': 23, 'Marina District': 17,
            'Richmond District': 10, 'Sunset District': 15, 'Golden Gate Park': 7
        },
        'Mission District': {
            'Haight-Ashbury': 12, 'Union Square': 15, 'Pacific Heights': 16,
            'Bayview': 14, 'Fisherman\'s Wharf': 22, 'Marina District': 19,
            'Richmond District': 20, 'Sunset District': 24, 'Golden Gate Park': 17
        },
        'Union Square': {
            'Haight-Ashbury': 18, 'Mission District': 14, 'Pacific Heights': 15,
            'Bayview': 15, 'Fisherman\'s Wharf': 15, 'Marina District': 18,
            'Richmond District': 20, 'Sunset District': 27, 'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11, 'Mission District': 15, 'Union Square': 12,
            'Bayview': 22, 'Fisherman\'s Wharf': 13, 'Marina District': 6,
            'Richmond District': 12, 'Sunset District': 21, 'Golden Gate Park': 15
        },
        'Bayview': {
            'Haight-Ashbury': 19, 'Mission District': 13, 'Union Square': 18,
            'Pacific Heights': 23, 'Fisherman\'s Wharf': 25, 'Marina District': 27,
            'Richmond District': 25, 'Sunset District': 23, 'Golden Gate Park': 22
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22, 'Mission District': 22, 'Union Square': 13,
            'Pacific Heights': 12, 'Bayview': 26, 'Marina District': 9,
            'Richmond District': 18, 'Sunset District': 27, 'Golden Gate Park': 25
        },
        'Marina District': {
            'Haight-Ashbury': 16, 'Mission District': 20, 'Union Square': 16,
            'Pacific Heights': 7, 'Bayview': 27, 'Fisherman\'s Wharf': 10,
            'Richmond District': 11, 'Sunset District': 19, 'Golden Gate Park': 18
        },
        'Richmond District': {
            'Haight-Ashbury': 10, 'Mission District': 20, 'Union Square': 21,
            'Pacific Heights': 10, 'Bayview': 27, 'Fisherman\'s Wharf': 18,
            'Marina District': 9, 'Sunset District': 11, 'Golden Gate Park': 9
        },
        'Sunset District': {
            'Haight-Ashbury': 15, 'Mission District': 25, 'Union Square': 30,
            'Pacific Heights': 21, 'Bayview': 22, 'Fisherman\'s Wharf': 29,
            'Marina District': 21, 'Richmond District': 12, 'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7, 'Mission District': 17, 'Union Square': 22,
            'Pacific Heights': 16, 'Bayview': 23, 'Fisherman\'s Wharf': 24,
            'Marina District': 16, 'Richmond District': 7, 'Sunset District': 10
        }
    }

    # Define friends' availability and meeting requirements
    friends = [
        {'name': 'Elizabeth', 'location': 'Mission District', 'start': 10.5, 'end': 20.0, 'duration': 1.5},
        {'name': 'David', 'location': 'Union Square', 'start': 15.25, 'end': 19.0, 'duration': 0.75},
        {'name': 'Sandra', 'location': 'Pacific Heights', 'start': 7.0, 'end': 20.0, 'duration': 2.0},
        {'name': 'Thomas', 'location': 'Bayview', 'start': 19.5, 'end': 20.5, 'duration': 0.5},
        {'name': 'Robert', 'location': 'Fisherman\'s Wharf', 'start': 10.0, 'end': 15.0, 'duration': 0.25},
        {'name': 'Kenneth', 'location': 'Marina District', 'start': 10.75, 'end': 13.0, 'duration': 0.75},
        {'name': 'Melissa', 'location': 'Richmond District', 'start': 18.25, 'end': 20.0, 'duration': 0.25},
        {'name': 'Kimberly', 'location': 'Sunset District', 'start': 10.25, 'end': 18.25, 'duration': 1.75},
        {'name': 'Amanda', 'location': 'Golden Gate Park', 'start': 7.75, 'end': 18.75, 'duration': 0.25}
    ]

    # Create constraint problem
    problem = Problem()

    # Add position variables (order of visits)
    positions = list(range(len(friends)))
    problem.addVariables(positions, positions)
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Add start time variables for each friend
    for friend in friends:
        name = friend['name']
        start_window = friend['start']
        end_window = friend['end']
        duration = friend['duration']
        
        # Calculate possible start times (in 15-minute increments)
        possible_starts = []
        current_time = start_window
        while current_time + duration <= end_window:
            possible_starts.append(round(current_time, 2))
            current_time += 0.25  # 15 minutes
        
        if possible_starts:
            problem.addVariable(f"{name}_start", possible_starts)

    # Add constraints for ordering and travel times
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # Constraint: if friend i comes before friend j in sequence,
                # then j's start time must be >= i's end time + travel time
                def ordering_constraint(pos_i, pos_j, start_i, start_j, i=i, j=j):
                    if pos_i < pos_j:  # i comes before j
                        loc_i = friends[i]['location']
                        loc_j = friends[j]['location']
                        travel_time = travel_times[loc_i][loc_j] / 60.0
                        end_i = start_i + friends[i]['duration']
                        return start_j >= end_i + travel_time
                    return True  # No constraint if i comes after j
                
                problem.addConstraint(
                    ordering_constraint,
                    [i, j, f"{friends[i]['name']}_start", f"{friends[j]['name']}_start"]
                )

    # Add constraint for starting from Haight-Ashbury
    # The first friend in sequence must account for travel from Haight-Ashbury
    def first_friend_constraint(*position_values):
        # Find which friend is first
        first_index = position_values.index(0)
        first_friend = friends[first_index]
        first_start_var = f"{first_friend['name']}_start"
        
        # This will be handled by the start time domain restriction
        # The actual constraint is applied through the start time possibilities
        return True
    
    problem.addConstraint(first_friend_constraint, positions)

    # Additional constraint: first friend's start time must allow for travel from Haight-Ashbury
    for i, friend in enumerate(friends):
        travel_from_start = travel_times['Haight-Ashbury'][friend['location']] / 60.0
        earliest_possible = 9.0 + travel_from_start
        
        def start_after_travel(start_time, earliest=earliest_possible):
            return start_time >= earliest
        
        problem.addConstraint(start_after_travel, [f"{friend['name']}_start"])

    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Use the first solution found
        solution = solutions[0]
        
        # Create itinerary by sorting friends by their position
        itinerary = []
        position_to_friend = {}
        
        for i in range(len(friends)):
            position_to_friend[solution[i]] = friends[i]
        
        for pos in sorted(position_to_friend.keys()):
            friend = position_to_friend[pos]
            start_time_var = f"{friend['name']}_start"
            start_time = solution[start_time_var]
            end_time = start_time + friend['duration']
            
            # Convert decimal hours to time string
            start_hour = int(start_time)
            start_minute = int(round((start_time - start_hour) * 60))
            end_hour = int(end_time)
            end_minute = int(round((end_time - end_hour) * 60))
            
            # Handle minute overflow
            if start_minute == 60:
                start_hour += 1
                start_minute = 0
            if end_minute == 60:
                end_hour += 1
                end_minute = 0
            
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()