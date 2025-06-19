import json
from datetime import datetime, timedelta

def calculate_travel_time(distance):
    # Assuming travel time is equal to distance for simplicity
    return distance

def is_valid_meeting(start_time, end_time, person, location, constraints):
    meeting_duration = end_time - start_time
    for constraint in constraints:
        if constraint['person'] == person and constraint['location'] == location:
            return meeting_duration >= timedelta(minutes=constraint['duration'])
    return False

def find_optimal_schedule(constraints, locations, travel_times):
    # Initialize schedule
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = locations[0]
    
    # Visit locations in order of proximity to current location
    locations_to_visit = locations[1:]
    
    for location in locations_to_visit:
        # Check if person is available at this location
        for constraint in constraints:
            if constraint['location'] == location:
                start_time = datetime.strptime(constraint['start_time'], '%H:%M')
                end_time = datetime.strptime(constraint['end_time'], '%H:%M')
                if start_time <= current_time < end_time:
                    # Check if meeting duration is sufficient
                    meeting_duration = end_time - current_time
                    if meeting_duration >= timedelta(minutes=constraint['duration']):
                        # Add meeting to schedule
                        schedule.append({
                            'action':'meet',
                            'location': location,
                            'person': constraint['person'],
                           'start_time': current_time.strftime('%H:%M'),
                            'end_time': end_time.strftime('%H:%M')
                        })
                        current_time = end_time
                        break
        
        # Update current location and time
        if location!= current_location:
            travel_time = calculate_travel_time(travel_times[current_location][location])
            current_time += timedelta(minutes=travel_time)
        
        current_location = location
    
    return schedule

def main():
    # Define input parameters
    travel_times = {
        'North Beach': {'Mission District': 18, 'The Castro': 22},
        'Mission District': {'North Beach': 17, 'The Castro': 7},
        'The Castro': {'North Beach': 20, 'Mission District': 7}
    }
    constraints = [
        {'person': 'James', 'location': 'Mission District','start_time': '12:45', 'end_time': '14:00', 'duration': 75},
        {'person': 'Robert', 'location': 'The Castro','start_time': '12:45', 'end_time': '14:30', 'duration': 30}
    ]
    locations = ['North Beach', 'Mission District', 'The Castro']
    
    # Calculate optimal schedule
    schedule = find_optimal_schedule(constraints, locations, travel_times)
    
    # Print result as JSON
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == '__main__':
    main()