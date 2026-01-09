import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Marina District': {
            'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15,
            'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17,
            'Haight-Ashbury': 16, 'Mission District': 20
        },
        'Embarcadero': {
            'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7,
            'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5,
            'Haight-Ashbury': 21, 'Mission District': 20
        },
        'Bayview': {
            'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19,
            'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19,
            'Haight-Ashbury': 19, 'Mission District': 13
        },
        'Union Square': {
            'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7,
            'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9,
            'Haight-Ashbury': 18, 'Mission District': 14
        },
        'Chinatown': {
            'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7,
            'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5,
            'Haight-Ashbury': 19, 'Mission District': 17
        },
        'Sunset District': {
            'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30,
            'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30,
            'Haight-Ashbury': 15, 'Mission District': 25
        },
        'Golden Gate Park': {
            'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22,
            'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26,
            'Haight-Ashbury': 7, 'Mission District': 17
        },
        'Financial District': {
            'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9,
            'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23,
            'Haight-Ashbury': 19, 'Mission District': 17
        },
        'Haight-Ashbury': {
            'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19,
            'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7,
            'Financial District': 21, 'Mission District': 11
        },
        'Mission District': {
            'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15,
            'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17,
            'Financial District': 15, 'Haight-Ashbury': 12
        }
    }

    # Define meeting constraints
    meetings = [
        {'person': 'Joshua', 'location': 'Embarcadero', 'start_window': '9:45', 'end_window': '18:00', 'duration': 105},
        {'person': 'Jeffrey', 'location': 'Bayview', 'start_window': '9:45', 'end_window': '20:15', 'duration': 75},
        {'person': 'Charles', 'location': 'Union Square', 'start_window': '10:45', 'end_window': '20:15', 'duration': 120},
        {'person': 'Joseph', 'location': 'Chinatown', 'start_window': '7:00', 'end_window': '15:30', 'duration': 60},
        {'person': 'Elizabeth', 'location': 'Sunset District', 'start_window': '9:00', 'end_window': '9:45', 'duration': 45},
        {'person': 'Matthew', 'location': 'Golden Gate Park', 'start_window': '11:00', 'end_window': '19:30', 'duration': 45},
        {'person': 'Carol', 'location': 'Financial District', 'start_window': '10:45', 'end_window': '11:15', 'duration': 15},
        {'person': 'Paul', 'location': 'Haight-Ashbury', 'start_window': '19:15', 'end_window': '20:30', 'duration': 15},
        {'person': 'Rebecca', 'location': 'Mission District', 'start_window': '17:00', 'end_window': '21:45', 'duration': 45}
    ]

    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return hours * 60 + minutes
        return int(time_str) * 60

    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Create problem
    problem = constraint.Problem()

    # Add variables for start times of each meeting
    for i, meeting in enumerate(meetings):
        start_window = time_to_minutes(meeting['start_window'])
        end_window = time_to_minutes(meeting['end_window'])
        # Only add meetings that are possible within their windows
        if end_window - start_window >= meeting['duration']:
            problem.addVariable(f'start_{i}', range(start_window, end_window - meeting['duration'] + 1))

    # Add travel time constraints
    meeting_vars = [f'start_{i}' for i in range(len(meetings)) if f'start_{i}' in problem._variables]
    
    def travel_constraint(*starts):
        # Create list of (start_time, end_time, location) for each meeting
        schedule = []
        for idx, start in enumerate(starts):
            meeting_idx = int(meeting_vars[idx].split('_')[1])
            meeting = meetings[meeting_idx]
            schedule.append((start, start + meeting['duration'], meeting['location']))
        
        # Sort by start time
        schedule.sort()
        
        # Check travel times between consecutive meetings
        for i in range(len(schedule) - 1):
            end_current = schedule[i][1]
            start_next = schedule[i + 1][0]
            loc_current = schedule[i][2]
            loc_next = schedule[i + 1][2]
            
            travel_time = travel_times[loc_current][loc_next]
            
            if start_next < end_current + travel_time:
                return False
        
        return True

    if len(meeting_vars) > 1:
        problem.addConstraint(travel_constraint, meeting_vars)

    # Find solution that maximizes number of meetings
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many as possible
        best_solution = {}
    else:
        best_solution = max(solutions, key=lambda x: len(x))

    # Build itinerary
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Marina District'
    
    # Sort meetings by their start times in the solution
    scheduled_meetings = []
    for var, start_time in best_solution.items():
        idx = int(var.split('_')[1])
        meeting = meetings[idx]
        scheduled_meetings.append((start_time, meeting))
    
    scheduled_meetings.sort()
    
    for start_time, meeting in scheduled_meetings:
        # Add travel time if needed
        if current_location != meeting['location']:
            travel_time = travel_times[current_location][meeting['location']]
            travel_start = minutes_to_time(current_time)
            current_time += travel_time
            travel_end = minutes_to_time(current_time)
            itinerary.append({
                "action": "travel",
                "location": meeting['location'],
                "person": "",
                "start_time": travel_start,
                "end_time": travel_end
            })
            current_location = meeting['location']
        
        # Add meeting
        meeting_start = minutes_to_time(start_time)
        meeting_end = minutes_to_time(start_time + meeting['duration'])
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        current_time = start_time + meeting['duration']
        current_location = meeting['location']

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()