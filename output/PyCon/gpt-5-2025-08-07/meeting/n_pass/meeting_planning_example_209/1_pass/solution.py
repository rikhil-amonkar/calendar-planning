import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'North Beach'): 29,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'North Beach'): 5,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Russian Hill'): 4
    }
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time_base = 540  # 9:00 AM in minutes
    
    # Friend constraints (in minutes since base time)
    anthony_window_start = 795  # 1:15 PM = 13*60 + 15 = 795 minutes
    anthony_window_end = 870    # 2:30 PM = 14*60 + 30 = 870 minutes
    anthony_min_duration = 60
    
    rebecca_window_start = 1170  # 7:30 PM = 19*60 + 30 = 1170 minutes
    rebecca_window_end = 1275    # 9:15 PM = 21*60 + 15 = 1275 minutes
    rebecca_min_duration = 105
    
    melissa_window_start = 495   # 8:15 AM = 8*60 + 15 = 495 minutes
    melissa_window_end = 810     # 1:30 PM = 13*60 + 30 = 810 minutes
    melissa_min_duration = 105
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting (in minutes since base)
    # We'll use -1 to indicate not meeting that person
    problem.addVariable('melissa_start', list(range(melissa_window_start, melissa_window_end - melissa_min_duration + 1)) + [-1])
    problem.addVariable('anthony_start', list(range(anthony_window_start, anthony_window_end - anthony_min_duration + 1)) + [-1])
    problem.addVariable('rebecca_start', list(range(rebecca_window_start, rebecca_window_end - rebecca_min_duration + 1)) + [-1])
    
    # Calculate end times
    def get_end_time(start_time, min_duration):
        if start_time == -1:
            return -1
        return start_time + min_duration
    
    # Constraint: No overlapping meetings when considering travel
    def no_overlap_with_travel(m_start, a_start, r_start):
        meetings = []
        
        if m_start != -1:
            meetings.append(('Melissa', m_start, get_end_time(m_start, melissa_min_duration), 'North Beach'))
        if a_start != -1:
            meetings.append(('Anthony', a_start, get_end_time(a_start, anthony_min_duration), 'Chinatown'))
        if r_start != -1:
            meetings.append(('Rebecca', r_start, get_end_time(r_start, rebecca_min_duration), 'Russian Hill'))
        
        # Sort by start time
        meetings.sort(key=lambda x: x[1])
        
        # Check if we can make all meetings considering travel
        current_location = 'Sunset District'
        current_time = start_time_base
        
        for i, (person, start, end, location) in enumerate(meetings):
            # Travel to meeting
            travel_time = travel_times.get((current_location, location), 0)
            
            # If we can't reach the meeting on time, invalid
            if current_time + travel_time > start:
                return False
            
            # Update current time and location
            current_time = end
            current_location = location
            
            # Check if we need to travel to next meeting
            if i < len(meetings) - 1:
                next_person, next_start, next_end, next_location = meetings[i + 1]
                travel_to_next = travel_times.get((location, next_location), 0)
                
                # If we can't make it to next meeting, invalid
                if end + travel_to_next > next_start:
                    return False
        
        return True
    
    problem.addConstraint(no_overlap_with_travel, ['melissa_start', 'anthony_start', 'rebecca_start'])
    
    # Objective: maximize number of meetings
    def count_meetings(m_start, a_start, r_start):
        count = 0
        if m_start != -1:
            count += 1
        if a_start != -1:
            count += 1
        if r_start != -1:
            count += 1
        return count
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to find any valid schedule
        result = {"itinerary": []}
        print(json.dumps(result))
        return
    
    # Find solution with maximum meetings
    best_solution = max(solutions, key=lambda sol: count_meetings(sol['melissa_start'], sol['anthony_start'], sol['rebecca_start']))
    
    # Build itinerary
    itinerary = []
    current_location = 'Sunset District'
    current_time = start_time_base
    
    # Helper function to convert minutes to time string
    def minutes_to_time(minutes):
        base_time = datetime(2024, 1, 1, 9, 0)  # Start at 9:00 AM
        target_time = base_time + timedelta(minutes=minutes)
        return target_time.strftime('%H:%M').lstrip('0')
    
    # Process meetings in chronological order
    meetings = []
    if best_solution['melissa_start'] != -1:
        meetings.append(('Melissa', best_solution['melissa_start'], 
                        get_end_time(best_solution['melissa_start'], melissa_min_duration), 'North Beach'))
    if best_solution['anthony_start'] != -1:
        meetings.append(('Anthony', best_solution['anthony_start'], 
                        get_end_time(best_solution['anthony_start'], anthony_min_duration), 'Chinatown'))
    if best_solution['rebecca_start'] != -1:
        meetings.append(('Rebecca', best_solution['rebecca_start'], 
                        get_end_time(best_solution['rebecca_start'], rebecca_min_duration), 'Russian Hill'))
    
    # Sort by start time
    meetings.sort(key=lambda x: x[1])
    
    for person, start, end, location in meetings:
        # Add travel if needed
        if current_location != location:
            travel_time = travel_times.get((current_location, location), 0)
            travel_start = minutes_to_time(current_time)
            travel_end = minutes_to_time(current_time + travel_time)
            itinerary.append({
                "action": "travel",
                "location": location,
                "start_time": travel_start,
                "end_time": travel_end
            })
            current_time += travel_time
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        current_location = location
        current_time = end
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()