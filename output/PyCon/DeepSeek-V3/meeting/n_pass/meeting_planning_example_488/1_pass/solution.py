import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 25,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Sunset District'): 15
    }
    
    # Friend constraints
    friends = {
        'Ronald': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('10:00', '%H:%M'),
            'available_end': datetime.strptime('17:00', '%H:%M'),
            'min_duration': 105
        },
        'Sarah': {
            'location': 'Russian Hill',
            'available_start': datetime.strptime('7:15', '%H:%M'),
            'available_end': datetime.strptime('9:30', '%H:%M'),
            'min_duration': 45
        },
        'Helen': {
            'location': 'The Castro',
            'available_start': datetime.strptime('13:30', '%H:%M'),
            'available_end': datetime.strptime('17:00', '%H:%M'),
            'min_duration': 120
        },
        'Joshua': {
            'location': 'Sunset District',
            'available_start': datetime.strptime('14:15', '%H:%M'),
            'available_end': datetime.strptime('19:30', '%H:%M'),
            'min_duration': 90
        },
        'Margaret': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('10:15', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 60
        }
    }
    
    # Start at Pacific Heights at 9:00 AM
    start_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Pacific Heights'
    
    problem = constraint.Problem()
    
    # Define variables for each friend: start time (in minutes from 9:00)
    friend_names = list(friends.keys())
    
    # Add variables for start times (in minutes from 9:00)
    for friend in friend_names:
        available_start = friends[friend]['available_start']
        available_end = friends[friend]['available_end']
        
        # Convert to minutes from 9:00
        start_min = max(0, (available_start - start_time).total_seconds() // 60)
        end_min = (available_end - start_time).total_seconds() // 60
        
        problem.addVariable(f"{friend}_start", range(int(start_min), int(end_min) + 1))
        problem.addVariable(f"{friend}_duration", [friends[friend]['min_duration']])
    
    # Define the order of visits
    visit_order = ['Sarah', 'Ronald', 'Margaret', 'Helen', 'Joshua']
    
    # Add constraints for travel time and scheduling
    for i in range(len(visit_order) - 1):
        current_friend = visit_order[i]
        next_friend = visit_order[i + 1]
        
        current_loc = friends[current_friend]['location']
        next_loc = friends[next_friend]['location']
        travel_time = travel_times[(current_loc, next_loc)]
        
        def travel_constraint(current_end, next_start, travel=travel_time):
            return current_end + travel <= next_start
        
        problem.addConstraint(
            travel_constraint,
            [f"{current_friend}_end", f"{next_friend}_start"]
        )
    
    # Add constraint that meeting end = start + duration
    for friend in friend_names:
        def meeting_constraint(start, duration, f=friend):
            return start + duration
        
        problem.addVariable(f"{friend}_end", meeting_constraint)
        problem.addConstraint(
            lambda start, end, duration: end == start + duration,
            [f"{friend}_start", f"{friend}_end", f"{friend}_duration"]
        )
    
    # Add constraint that meetings must fit within available time windows
    for friend in friend_names:
        available_start = friends[friend]['available_start']
        available_end = friends[friend]['available_end']
        
        start_min = max(0, (available_start - start_time).total_seconds() // 60)
        end_min = (available_end - start_time).total_seconds() // 60
        
        def time_window_constraint(start, end, f=friend, start_lim=start_min, end_lim=end_min):
            return start >= start_lim and end <= end_lim
        
        problem.addConstraint(
            time_window_constraint,
            [f"{friend}_start", f"{friend}_end"]
        )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with adjusted constraints
        itinerary = []
        current_time = start_time
        current_loc = 'Pacific Heights'
        
        # Try to visit Sarah first (she has the earliest availability)
        sarah = friends['Sarah']
        travel_time = travel_times[(current_loc, sarah['location'])]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        if arrival_time <= sarah['available_end']:
            meeting_start = max(arrival_time, sarah['available_start'])
            meeting_end = meeting_start + timedelta(minutes=min(sarah['min_duration'], 
                                                              (sarah['available_end'] - meeting_start).total_seconds() // 60))
            if meeting_end <= sarah['available_end']:
                itinerary.append({
                    "action": "meet",
                    "location": sarah['location'],
                    "person": "Sarah",
                    "start_time": meeting_start.strftime('%H:%M'),
                    "end_time": meeting_end.strftime('%H:%M')
                })
                current_time = meeting_end
                current_loc = sarah['location']
        
        # Try to meet Ronald
        ronald = friends['Ronald']
        travel_time = travel_times[(current_loc, ronald['location'])]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        if arrival_time <= ronald['available_end']:
            meeting_start = max(arrival_time, ronald['available_start'])
            meeting_end = meeting_start + timedelta(minutes=min(ronald['min_duration'], 
                                                              (ronald['available_end'] - meeting_start).total_seconds() // 60))
            if meeting_end <= ronald['available_end']:
                itinerary.append({
                    "action": "meet",
                    "location": ronald['location'],
                    "person": "Ronald",
                    "start_time": meeting_start.strftime('%H:%M'),
                    "end_time": meeting_end.strftime('%H:%M')
                })
                current_time = meeting_end
                current_loc = ronald['location']
        
        # Continue with other friends...
        
        result = {"itinerary": itinerary}
    else:
        # Use the first valid solution
        solution = solutions[0]
        itinerary = []
        
        # Sort visits by start time
        visits = []
        for friend in friend_names:
            start_minutes = solution[f"{friend}_start"]
            duration = solution[f"{friend}_duration"]
            start_time_actual = start_time + timedelta(minutes=start_minutes)
            end_time_actual = start_time_actual + timedelta(minutes=duration)
            
            visits.append({
                "friend": friend,
                "location": friends[friend]['location'],
                "start": start_time_actual,
                "end": end_time_actual
            })
        
        visits.sort(key=lambda x: x['start'])
        
        for visit in visits:
            itinerary.append({
                "action": "meet",
                "location": visit['location'],
                "person": visit['friend'],
                "start_time": visit['start'].strftime('%H:%M'),
                "end_time": visit['end'].strftime('%H:%M')
            })
        
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()