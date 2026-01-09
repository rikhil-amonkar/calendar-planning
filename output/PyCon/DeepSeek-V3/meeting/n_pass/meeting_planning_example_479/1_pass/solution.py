import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define travel times between locations (in minutes)
    travel_times = {
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Financial District'): 5,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Financial District'): 19,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Financial District'): 23,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Presidio'): 22
    }

    # Define meeting constraints
    meetings = [
        {
            'person': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('8:45', '%H:%M'),
            'available_end': datetime.strptime('11:45', '%H:%M'),
            'min_duration': 45
        },
        {
            'person': 'Kevin',
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('10:15', '%H:%M'),
            'available_end': datetime.strptime('16:15', '%H:%M'),
            'min_duration': 90
        },
        {
            'person': 'Deborah',
            'location': 'Bayview',
            'available_start': datetime.strptime('15:00', '%H:%M'),
            'available_end': datetime.strptime('19:15', '%H:%M'),
            'min_duration': 120
        },
        {
            'person': 'Stephanie',
            'location': 'Presidio',
            'available_start': datetime.strptime('10:00', '%H:%M'),
            'available_end': datetime.strptime('17:15', '%H:%M'),
            'min_duration': 120
        },
        {
            'person': 'Emily',
            'location': 'Financial District',
            'available_start': datetime.strptime('11:30', '%H:%M'),
            'available_end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 105
        }
    ]

    # Create problem instance
    problem = constraint.Problem()

    # Define variables for each meeting: start time (in minutes from 9:00)
    start_time_9am = datetime.strptime('9:00', '%H:%M')
    
    # We'll use a simplified approach - try different permutations of meeting order
    # Since python-constraint doesn't handle time windows well, we'll use a brute force approach
    
    best_schedule = None
    max_meetings = 0
    
    # Try all permutations of meeting order
    from itertools import permutations
    
    for meeting_order in permutations(range(len(meetings))):
        current_time = start_time_9am
        schedule = []
        valid = True
        
        for meeting_idx in meeting_order:
            meeting = meetings[meeting_idx]
            
            # Calculate travel time
            if not schedule:
                # First meeting, travel from Embarcadero
                travel_time = travel_times[('Embarcadero', meeting['location'])]
            else:
                # Travel from previous location
                prev_location = schedule[-1]['location']
                travel_time = travel_times[(prev_location, meeting['location'])]
            
            # Add travel time
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # Check if we arrive within available window
            if arrival_time < meeting['available_start']:
                start_time = meeting['available_start']
            else:
                start_time = arrival_time
            
            # Calculate end time
            end_time = start_time + timedelta(minutes=meeting['min_duration'])
            
            # Check if meeting fits in available window
            if end_time > meeting['available_end']:
                valid = False
                break
            
            # Add to schedule
            schedule.append({
                'person': meeting['person'],
                'location': meeting['location'],
                'start_time': start_time,
                'end_time': end_time
            })
            
            # Update current time
            current_time = end_time
        
        if valid and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    # If no valid schedule found with all meetings, try with fewer meetings
    if best_schedule is None:
        # Try subsets of meetings
        from itertools import combinations
        
        for num_meetings in range(len(meetings), 0, -1):
            for meeting_subset in combinations(range(len(meetings)), num_meetings):
                for meeting_order in permutations(meeting_subset):
                    current_time = start_time_9am
                    schedule = []
                    valid = True
                    
                    for meeting_idx in meeting_order:
                        meeting = meetings[meeting_idx]
                        
                        # Calculate travel time
                        if not schedule:
                            travel_time = travel_times[('Embarcadero', meeting['location'])]
                        else:
                            prev_location = schedule[-1]['location']
                            travel_time = travel_times[(prev_location, meeting['location'])]
                        
                        arrival_time = current_time + timedelta(minutes=travel_time)
                        
                        if arrival_time < meeting['available_start']:
                            start_time = meeting['available_start']
                        else:
                            start_time = arrival_time
                        
                        end_time = start_time + timedelta(minutes=meeting['min_duration'])
                        
                        if end_time > meeting['available_end']:
                            valid = False
                            break
                        
                        schedule.append({
                            'person': meeting['person'],
                            'location': meeting['location'],
                            'start_time': start_time,
                            'end_time': end_time
                        })
                        
                        current_time = end_time
                    
                    if valid:
                        best_schedule = schedule
                        break
                if best_schedule is not None:
                    break
            if best_schedule is not None:
                break

    # Format output
    if best_schedule:
        itinerary = []
        for meeting in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": meeting['start_time'].strftime('%H:%M'),
                "end_time": meeting['end_time'].strftime('%H:%M')
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()