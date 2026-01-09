from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17
    }
    
    # Friend constraints
    friends = {
        'Sarah': {
            'location': 'Sunset District',
            'available_start': datetime.strptime('10:45', '%H:%M'),
            'available_end': datetime.strptime('19:00', '%H:%M'),
            'min_duration': 30  # minutes
        },
        'Richard': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('11:45', '%H:%M'),
            'available_end': datetime.strptime('15:45', '%H:%M'),
            'min_duration': 90
        },
        'Elizabeth': {
            'location': 'Mission District',
            'available_start': datetime.strptime('11:00', '%H:%M'),
            'available_end': datetime.strptime('17:15', '%H:%M'),
            'min_duration': 120
        },
        'Michelle': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('18:15', '%H:%M'),
            'available_end': datetime.strptime('20:45', '%H:%M'),
            'min_duration': 90
        }
    }
    
    # Start location and time
    start_location = 'Richmond District'
    start_time = datetime.strptime('9:00', '%H:%M')
    
    # Sort friends by availability window (earlier available_start first)
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]['available_start'])
    
    itinerary = []
    current_time = start_time
    current_location = start_location
    scheduled_friends = set()
    
    # Try to schedule each friend
    for friend_name, friend_info in sorted_friends:
        if friend_name in scheduled_friends:
            continue
            
        location = friend_info['location']
        available_start = friend_info['available_start']
        available_end = friend_info['available_end']
        min_duration = friend_info['min_duration']
        
        # Calculate travel time to this friend
        travel_time = travel_times.get((current_location, location), 30)
        
        # Earliest we can start this meeting (after travel)
        earliest_start = max(available_start, current_time + timedelta(minutes=travel_time))
        
        # Check if we can schedule this meeting
        if earliest_start + timedelta(minutes=min_duration) <= available_end:
            # Schedule the meeting
            meeting_start = earliest_start
            meeting_end = earliest_start + timedelta(minutes=min_duration)
            
            # Add travel segment if needed
            if current_location != location and meeting_start > current_time:
                travel_end_time = meeting_start
                travel_start_time = meeting_start - timedelta(minutes=travel_time)
                if travel_start_time > current_time:
                    itinerary.append({
                        "action": "travel",
                        "location": location,
                        "person": "",
                        "start_time": travel_start_time.strftime('%H:%M'),
                        "end_time": travel_end_time.strftime('%H:%M')
                    })
            
            # Add the meeting
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend_name,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            
            # Update current state
            current_time = meeting_end
            current_location = location
            scheduled_friends.add(friend_name)
    
    # Try to optimize by checking if we can fit more friends in gaps
    # Create a list of all possible friend combinations
    all_friends = list(friends.keys())
    
    # Simple optimization: try to add unscheduled friends between existing meetings
    if len(scheduled_friends) < len(all_friends):
        unscheduled = [f for f in all_friends if f not in scheduled_friends]
        
        # Try to insert unscheduled friends between existing itinerary items
        new_itinerary = []
        i = 0
        
        while i < len(itinerary):
            new_itinerary.append(itinerary[i])
            
            # Check if there's a gap after this item for another meeting
            if i < len(itinerary) - 1:
                current_end = datetime.strptime(itinerary[i]['end_time'], '%H:%M')
                next_start = datetime.strptime(itinerary[i+1]['start_time'], '%H:%M')
                gap_duration = (next_start - current_end).total_seconds() / 60
                
                current_loc = itinerary[i]['location']
                
                # Try to find an unscheduled friend that fits in this gap
                for friend_name in unscheduled[:]:  # Copy for safe removal
                    friend_info = friends[friend_name]
                    
                    if (current_end >= friend_info['available_start'] and 
                        current_end + timedelta(minutes=friend_info['min_duration']) <= friend_info['available_end'] and
                        current_end + timedelta(minutes=friend_info['min_duration']) <= next_start):
                        
                        # Check travel time
                        travel_time = travel_times.get((current_loc, friend_info['location']), 30)
                        
                        if (current_end + timedelta(minutes=travel_time + friend_info['min_duration']) <= next_start and
                            current_end + timedelta(minutes=travel_time) >= friend_info['available_start']):
                            
                            # Schedule this friend in the gap
                            meeting_start = current_end + timedelta(minutes=travel_time)
                            meeting_end = meeting_start + timedelta(minutes=friend_info['min_duration'])
                            
                            # Add travel
                            new_itinerary.append({
                                "action": "travel",
                                "location": friend_info['location'],
                                "person": "",
                                "start_time": current_end.strftime('%H:%M'),
                                "end_time": meeting_start.strftime('%H:%M')
                            })
                            
                            # Add meeting
                            new_itinerary.append({
                                "action": "meet",
                                "location": friend_info['location'],
                                "person": friend_name,
                                "start_time": meeting_start.strftime('%H:%M'),
                                "end_time": meeting_end.strftime('%H:%M')
                            })
                            
                            # Update for next travel
                            travel_back_time = travel_times.get((friend_info['location'], itinerary[i+1]['location']), 30)
                            
                            # Add travel back to next meeting location if needed
                            if friend_info['location'] != itinerary[i+1]['location']:
                                travel_back_start = meeting_end
                                travel_back_end = travel_back_start + timedelta(minutes=travel_back_time)
                                
                                # Adjust next meeting start time if needed
                                if travel_back_end > next_start:
                                    # Shift the remaining itinerary
                                    shift_amount = travel_back_end - next_start
                                    for j in range(i+1, len(itinerary)):
                                        old_start = datetime.strptime(itinerary[j]['start_time'], '%H:%M')
                                        old_end = datetime.strptime(itinerary[j]['end_time'], '%H:%M')
                                        itinerary[j]['start_time'] = (old_start + shift_amount).strftime('%H:%M')
                                        itinerary[j]['end_time'] = (old_end + shift_amount).strftime('%H:%M')
                                
                                new_itinerary.append({
                                    "action": "travel",
                                    "location": itinerary[i+1]['location'],
                                    "person": "",
                                    "start_time": travel_back_start.strftime('%H:%M'),
                                    "end_time": travel_back_end.strftime('%H:%M')
                                })
                            
                            unscheduled.remove(friend_name)
                            break
            
            i += 1
        
        itinerary = new_itinerary
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()