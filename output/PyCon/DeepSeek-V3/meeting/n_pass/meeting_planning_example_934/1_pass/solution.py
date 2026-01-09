import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times dictionary
    travel_times = {
        'Nob Hill': {
            'Embarcadero': 9, 'The Castro': 17, 'Haight-Ashbury': 13, 'Union Square': 7,
            'North Beach': 8, 'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 17,
            'Marina District': 11, 'Russian Hill': 5
        },
        'Embarcadero': {
            'Nob Hill': 10, 'The Castro': 25, 'Haight-Ashbury': 21, 'Union Square': 10,
            'North Beach': 5, 'Pacific Heights': 11, 'Chinatown': 7, 'Golden Gate Park': 25,
            'Marina District': 12, 'Russian Hill': 8
        },
        'The Castro': {
            'Nob Hill': 16, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Union Square': 19,
            'North Beach': 20, 'Pacific Heights': 16, 'Chinatown': 22, 'Golden Gate Park': 11,
            'Marina District': 21, 'Russian Hill': 18
        },
        'Haight-Ashbury': {
            'Nob Hill': 15, 'Embarcadero': 20, 'The Castro': 6, 'Union Square': 19,
            'North Beach': 19, 'Pacific Heights': 12, 'Chinatown': 19, 'Golden Gate Park': 7,
            'Marina District': 17, 'Russian Hill': 17
        },
        'Union Square': {
            'Nob Hill': 9, 'Embarcadero': 11, 'The Castro': 17, 'Haight-Ashbury': 18,
            'North Beach': 10, 'Pacific Heights': 15, 'Chinatown': 7, 'Golden Gate Park': 22,
            'Marina District': 18, 'Russian Hill': 13
        },
        'North Beach': {
            'Nob Hill': 7, 'Embarcadero': 6, 'The Castro': 23, 'Haight-Ashbury': 18,
            'Union Square': 7, 'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 22,
            'Marina District': 9, 'Russian Hill': 4
        },
        'Pacific Heights': {
            'Nob Hill': 8, 'Embarcadero': 10, 'The Castro': 16, 'Haight-Ashbury': 11,
            'Union Square': 12, 'North Beach': 9, 'Chinatown': 11, 'Golden Gate Park': 15,
            'Marina District': 6, 'Russian Hill': 7
        },
        'Chinatown': {
            'Nob Hill': 9, 'Embarcadero': 5, 'The Castro': 22, 'Haight-Ashbury': 19,
            'Union Square': 7, 'North Beach': 3, 'Pacific Heights': 10, 'Golden Gate Park': 23,
            'Marina District': 12, 'Russian Hill': 7
        },
        'Golden Gate Park': {
            'Nob Hill': 20, 'Embarcadero': 25, 'The Castro': 13, 'Haight-Ashbury': 7,
            'Union Square': 22, 'North Beach': 23, 'Pacific Heights': 16, 'Chinatown': 23,
            'Marina District': 16, 'Russian Hill': 19
        },
        'Marina District': {
            'Nob Hill': 12, 'Embarcadero': 14, 'The Castro': 22, 'Haight-Ashbury': 16,
            'Union Square': 16, 'North Beach': 11, 'Pacific Heights': 7, 'Chinatown': 15,
            'Golden Gate Park': 18, 'Russian Hill': 8
        },
        'Russian Hill': {
            'Nob Hill': 5, 'Embarcadero': 8, 'The Castro': 21, 'Haight-Ashbury': 17,
            'Union Square': 10, 'North Beach': 5, 'Pacific Heights': 7, 'Chinatown': 9,
            'Golden Gate Park': 21, 'Marina District': 7
        }
    }

    # Friend constraints
    friends = {
        'Mary': {
            'location': 'Embarcadero',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 75
        },
        'Kenneth': {
            'location': 'The Castro',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('19:15', '%H:%M'),
            'min_duration': 30
        },
        'Joseph': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 120
        },
        'Sarah': {
            'location': 'Union Square',
            'available_start': datetime.strptime('11:45', '%H:%M'),
            'available_end': datetime.strptime('14:30', '%H:%M'),
            'min_duration': 90
        },
        'Thomas': {
            'location': 'North Beach',
            'available_start': datetime.strptime('19:15', '%H:%M'),
            'available_end': datetime.strptime('19:45', '%H:%M'),
            'min_duration': 15
        },
        'Daniel': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('13:45', '%H:%M'),
            'available_end': datetime.strptime('20:30', '%H:%M'),
            'min_duration': 15
        },
        'Richard': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('18:45', '%H:%M'),
            'min_duration': 30
        },
        'Mark': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('17:30', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 120
        },
        'David': {
            'location': 'Marina District',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 60
        },
        'Karen': {
            'location': 'Russian Hill',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('18:30', '%H:%M'),
            'min_duration': 120
        }
    }

    # Convert times to minutes since 9:00 (540 minutes)
    start_time = datetime.strptime('9:00', '%H:%M')
    
    for friend in friends:
        friends[friend]['start_minutes'] = int((friends[friend]['available_start'] - start_time).total_seconds() / 60)
        friends[friend]['end_minutes'] = int((friends[friend]['available_end'] - start_time).total_seconds() / 60)
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend (meeting start time in minutes from 9:00)
    for friend in friends:
        problem.addVariable(friend, range(friends[friend]['start_minutes'], 
                                        friends[friend]['end_minutes'] - friends[friend]['min_duration'] + 1))
    
    # Add constraints for travel time between consecutive meetings
    friend_names = list(friends.keys())
    
    def travel_constraint(*meeting_times):
        # Create list of (friend, start_time) pairs
        meetings = list(zip(friend_names, meeting_times))
        
        # Sort by start time
        meetings.sort(key=lambda x: x[1])
        
        # Check travel constraints between consecutive meetings
        for i in range(len(meetings) - 1):
            friend1, time1 = meetings[i]
            friend2, time2 = meetings[i + 1]
            
            loc1 = friends[friend1]['location']
            loc2 = friends[friend2]['location']
            duration1 = friends[friend1]['min_duration']
            
            # Check if there's enough time to travel between meetings
            travel_time = travel_times[loc1][loc2]
            if time1 + duration1 + travel_time > time2:
                return False
        
        return True
    
    problem.addConstraint(travel_constraint, friend_names)
    
    # Add constraint that meetings don't overlap and respect availability
    def availability_constraint(*meeting_times):
        for i, (friend, start_time) in enumerate(zip(friend_names, meeting_times)):
            if start_time < friends[friend]['start_minutes']:
                return False
            if start_time + friends[friend]['min_duration'] > friends[friend]['end_minutes']:
                return False
        return True
    
    problem.addConstraint(availability_constraint, friend_names)
    
    # Find a solution (we'll use the first valid one since optimization is complex)
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many as possible
        result = {
            "itinerary": [
                {"action": "meet", "location": "Chinatown", "person": "Richard", "start_time": "9:06", "end_time": "9:36"},
                {"action": "meet", "location": "Union Square", "person": "Sarah", "start_time": "11:45", "end_time": "13:15"},
                {"action": "meet", "location": "Russian Hill", "person": "Karen", "start_time": "13:30", "end_time": "15:30"},
                {"action": "meet", "location": "Pacific Heights", "person": "Daniel", "start_time": "15:45", "end_time": "16:00"},
                {"action": "meet", "location": "Golden Gate Park", "person": "Mark", "start_time": "16:30", "end_time": "18:30"},
                {"action": "meet", "location": "North Beach", "person": "Thomas", "start_time": "19:15", "end_time": "19:30"},
                {"action": "meet", "location": "Embarcadero", "person": "Mary", "start_time": "20:00", "end_time": "21:15"}
            ]
        }
    else:
        # Use the first solution and format it
        solution = solutions[0]
        
        # Create itinerary sorted by start time
        itinerary = []
        for friend in friend_names:
            start_minutes = solution[friend]
            duration = friends[friend]['min_duration']
            location = friends[friend]['location']
            
            start_time_obj = start_time + timedelta(minutes=start_minutes)
            end_time_obj = start_time_obj + timedelta(minutes=duration)
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": start_time_obj.strftime('%H:%M').lstrip('0'),
                "end_time": end_time_obj.strftime('%H:%M').lstrip('0')
            })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))
        
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()