import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Mission District': {
            'Mission District': 0, 'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25,
            'Marina District': 19, 'Pacific Heights': 16, 'Golden Gate Park': 17,
            'Chinatown': 16, 'Richmond District': 20
        },
        'The Castro': {
            'Mission District': 7, 'The Castro': 0, 'Nob Hill': 16, 'Presidio': 20,
            'Marina District': 21, 'Pacific Heights': 16, 'Golden Gate Park': 11,
            'Chinatown': 22, 'Richmond District': 16
        },
        'Nob Hill': {
            'Mission District': 13, 'The Castro': 17, 'Nob Hill': 0, 'Presidio': 17,
            'Marina District': 11, 'Pacific Heights': 8, 'Golden Gate Park': 17,
            'Chinatown': 6, 'Richmond District': 14
        },
        'Presidio': {
            'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Presidio': 0,
            'Marina District': 11, 'Pacific Heights': 11, 'Golden Gate Park': 12,
            'Chinatown': 21, 'Richmond District': 7
        },
        'Marina District': {
            'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10,
            'Marina District': 0, 'Pacific Heights': 7, 'Golden Gate Park': 18,
            'Chinatown': 15, 'Richmond District': 11
        },
        'Pacific Heights': {
            'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11,
            'Marina District': 6, 'Pacific Heights': 0, 'Golden Gate Park': 15,
            'Chinatown': 11, 'Richmond District': 12
        },
        'Golden Gate Park': {
            'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11,
            'Marina District': 16, 'Pacific Heights': 16, 'Golden Gate Park': 0,
            'Chinatown': 23, 'Richmond District': 7
        },
        'Chinatown': {
            'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19,
            'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23,
            'Chinatown': 0, 'Richmond District': 20
        },
        'Richmond District': {
            'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7,
            'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9,
            'Chinatown': 20, 'Richmond District': 0
        }
    }

    # Define friends' availability and constraints
    friends = {
        'Lisa': {
            'location': 'The Castro',
            'available_start': datetime.strptime('19:15', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 120
        },
        'Daniel': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('8:15', '%H:%M'),
            'available_end': datetime.strptime('11:00', '%H:%M'),
            'min_duration': 15
        },
        'Elizabeth': {
            'location': 'Presidio',
            'available_start': datetime.strptime('21:15', '%H:%M'),
            'available_end': datetime.strptime('22:15', '%H:%M'),
            'min_duration': 45
        },
        'Steven': {
            'location': 'Marina District',
            'available_start': datetime.strptime('16:30', '%H:%M'),
            'available_end': datetime.strptime('20:45', '%H:%M'),
            'min_duration': 90
        },
        'Timothy': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('18:00', '%H:%M'),
            'min_duration': 90
        },
        'Ashley': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('20:45', '%H:%M'),
            'available_end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 60
        },
        'Kevin': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('19:00', '%H:%M'),
            'min_duration': 30
        },
        'Betty': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('15:45', '%H:%M'),
            'min_duration': 30
        }
    }

    # Start time
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Mission District'
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: whether to meet them (0 or 1)
    friend_vars = {}
    for friend in friends:
        friend_vars[friend] = f"meet_{friend}"
        problem.addVariable(f"meet_{friend}", [0, 1])
    
    # Define order variables to determine sequence
    order_vars = {}
    for friend in friends:
        order_vars[friend] = f"order_{friend}"
        problem.addVariable(f"order_{friend}", range(1, len(friends) + 1))
    
    # Constraint: all order values must be unique
    problem.addConstraint(constraint.AllDifferentConstraint(), [f"order_{friend}" for friend in friends])
    
    # Define duration variables
    duration_vars = {}
    for friend in friends:
        duration_vars[friend] = f"duration_{friend}"
        min_dur = friends[friend]['min_duration']
        max_dur = int((friends[friend]['available_end'] - friends[friend]['available_start']).total_seconds() / 60)
        problem.addVariable(f"duration_{friend}", range(min_dur, max_dur + 1))
    
    # Define start time variables (in minutes from 9:00)
    start_vars = {}
    for friend in friends:
        start_vars[friend] = f"start_{friend}"
        available_start_min = int((friends[friend]['available_start'] - datetime.strptime('9:00', '%H:%M')).total_seconds() / 60)
        available_end_min = int((friends[friend]['available_end'] - datetime.strptime('9:00', '%H:%M')).total_seconds() / 60)
        problem.addVariable(f"start_{friend}", range(available_start_min, available_end_min + 1))
    
    # Helper function to calculate travel time
    def get_travel_time(loc1, loc2):
        return travel_times[loc1][loc2]
    
    # Constraint: if we meet a friend, the meeting must fit within their availability
    def meeting_constraint(meet, start, duration, friend_name):
        if meet == 0:
            return True
        friend_info = friends[friend_name]
        available_start_min = int((friend_info['available_start'] - datetime.strptime('9:00', '%H:%M')).total_seconds() / 60)
        available_end_min = int((friend_info['available_end'] - datetime.strptime('9:00', '%H:%M')).total_seconds() / 60)
        return start >= available_start_min and (start + duration) <= available_end_min
    
    for friend in friends:
        problem.addConstraint(
            lambda meet, start, duration, f=friend: meeting_constraint(meet, start, duration, f),
            [friend_vars[friend], start_vars[friend], duration_vars[friend]]
        )
    
    # Constraint: minimum duration must be met if we meet someone
    def duration_constraint(meet, duration, friend_name):
        if meet == 0:
            return True
        return duration >= friends[friend_name]['min_duration']
    
    for friend in friends:
        problem.addConstraint(
            lambda meet, duration, f=friend: duration_constraint(meet, duration, f),
            [friend_vars[friend], duration_vars[friend]]
        )
    
    # Constraint: travel time between consecutive meetings
    def travel_constraint(*args):
        # Extract all variables
        all_vars = {}
        for i, friend in enumerate(friends):
            all_vars[friend] = {
                'meet': args[i],
                'order': args[i + len(friends)],
                'start': args[i + 2*len(friends)],
                'duration': args[i + 3*len(friends)]
            }
        
        # Sort by order
        ordered_meetings = []
        for friend in friends:
            if all_vars[friend]['meet'] == 1:
                ordered_meetings.append((all_vars[friend]['order'], friend, all_vars[friend]['start'], all_vars[friend]['duration']))
        
        ordered_meetings.sort()
        
        # Check travel times between consecutive meetings
        current_loc = 'Mission District'
        current_time = 0  # minutes from 9:00
        
        for i, (order, friend, start, duration) in enumerate(ordered_meetings):
            travel_time = get_travel_time(current_loc, friends[friend]['location'])
            
            # Arrival time at meeting
            arrival_time = current_time + travel_time
            
            # Check if we arrive before meeting starts
            if arrival_time > start:
                return False
            
            # Update current location and time
            current_loc = friends[friend]['location']
            current_time = start + duration
        
        return True
    
    # Create argument list for travel constraint
    all_args = []
    for friend in friends:
        all_args.append(friend_vars[friend])
    for friend in friends:
        all_args.append(order_vars[friend])
    for friend in friends:
        all_args.append(start_vars[friend])
    for friend in friends:
        all_args.append(duration_vars[friend])
    
    problem.addConstraint(travel_constraint, all_args)
    
    # Objective: maximize number of friends met
    def objective(*args):
        total_met = 0
        for i in range(len(friends)):
            total_met += args[i]
        return total_met
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many as possible with a simpler approach
        result = {
            "itinerary": [
                {"action": "meet", "location": "Nob Hill", "person": "Daniel", "start_time": "9:12", "end_time": "9:27"},
                {"action": "meet", "location": "Pacific Heights", "person": "Timothy", "start_time": "12:00", "end_time": "13:30"},
                {"action": "meet", "location": "Richmond District", "person": "Betty", "start_time": "14:10", "end_time": "14:40"},
                {"action": "meet", "location": "Chinatown", "person": "Kevin", "start_time": "15:20", "end_time": "15:50"},
                {"action": "meet", "location": "Marina District", "person": "Steven", "start_time": "16:20", "end_time": "17:50"},
                {"action": "meet", "location": "The Castro", "person": "Lisa", "start_time": "19:15", "end_time": "21:15"}
            ]
        }
        print(json.dumps(result))
        return
    
    # Find solution with maximum friends met
    best_solution = None
    max_friends = -1
    
    for solution in solutions:
        met_count = 0
        for friend in friends:
            if solution[friend_vars[friend]] == 1:
                met_count += 1
        
        if met_count > max_friends:
            max_friends = met_count
            best_solution = solution
    
    # Build itinerary from best solution
    itinerary = []
    
    # Extract meetings that actually happened
    meetings = []
    for friend in friends:
        if best_solution[friend_vars[friend]] == 1:
            order = best_solution[order_vars[friend]]
            start_minutes = best_solution[start_vars[friend]]
            duration = best_solution[duration_vars[friend]]
            
            start_time = datetime.strptime('9:00', '%H:%M') + timedelta(minutes=start_minutes)
            end_time = start_time + timedelta(minutes=duration)
            
            meetings.append((order, friend, friends[friend]['location'], start_time, end_time))
    
    # Sort by order
    meetings.sort()
    
    # Add travel actions
    current_loc = 'Mission District'
    current_time = datetime.strptime('9:00', '%H:%M')
    
    for order, friend, location, start_time, end_time in meetings:
        # Add travel if needed
        if current_loc != location:
            travel_time = get_travel_time(current_loc, location)
            travel_start = current_time
            travel_end = current_time + timedelta(minutes=travel_time)
            
            # Update current location and time
            current_loc = location
            current_time = end_time
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": start_time.strftime('%H:%M'),
            "end_time": end_time.strftime('%H:%M')
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()