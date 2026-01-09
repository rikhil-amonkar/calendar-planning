import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from_row to column)
    travel_times = {
        'Fishermans Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fishermans Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fishermans Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fishermans Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }
    
    # Convert all times to minutes since midnight
    start_time = time_to_minutes('9:00')  # Arrival at Fisherman's Wharf
    
    # Friend availability windows
    melissa_available_start = time_to_minutes('8:30')
    melissa_available_end = time_to_minutes('20:00')
    melissa_min_duration = 15
    
    nancy_available_start = time_to_minutes('19:45')
    nancy_available_end = time_to_minutes('22:00')
    nancy_min_duration = 105
    
    emily_available_start = time_to_minutes('16:45')
    emily_available_end = time_to_minutes('22:00')
    emily_min_duration = 120
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Variables: start times for each meeting
    # We'll use minutes since midnight
    problem.addVariable('melissa_start', range(melissa_available_start, melissa_available_end - melissa_min_duration + 1))
    problem.addVariable('nancy_start', range(nancy_available_start, nancy_available_end - nancy_min_duration + 1))
    problem.addVariable('emily_start', range(emily_available_start, emily_available_end - emily_min_duration + 1))
    
    # Helper function to check if two meetings can be scheduled with travel time
    def can_schedule_meetings(start1, end1, loc1, start2, end2, loc2):
        travel_time = travel_times[loc1][loc2]
        return (start2 >= end1 + travel_time) or (start1 >= end2 + travel_time[loc2][loc1])
    
    # Constraints for meeting durations and availability
    def meeting_constraints(m_start, n_start, e_start):
        # Calculate end times
        m_end = m_start + melissa_min_duration
        n_end = n_start + nancy_min_duration
        e_end = e_start + emily_min_duration
        
        # Check if meetings fit within availability windows
        if not (melissa_available_start <= m_start <= melissa_available_end - melissa_min_duration):
            return False
        if not (nancy_available_start <= n_start <= nancy_available_end - nancy_min_duration):
            return False
        if not (emily_available_start <= e_start <= emily_available_end - emily_min_duration):
            return False
        
        # Check travel feasibility between meetings
        # We need to consider the order of meetings
        meetings = [
            ('Melissa', m_start, m_end, 'Golden Gate Park'),
            ('Nancy', n_start, n_end, 'Presidio'),
            ('Emily', e_start, e_end, 'Richmond District')
        ]
        
        # Sort meetings by start time to check travel feasibility
        meetings_sorted = sorted(meetings, key=lambda x: x[1])
        
        current_location = 'Fishermans Wharf'
        current_time = start_time
        
        for meeting in meetings_sorted:
            name, m_start, m_end, location = meeting
            
            # Check if we can travel to this meeting location
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + travel_time
            
            # We must arrive before or at the meeting start time
            if arrival_time > m_start:
                return False
            
            # Update current location and time
            current_location = location
            current_time = m_end
        
        return True
    
    problem.addConstraint(meeting_constraints, ['melissa_start', 'nancy_start', 'emily_start'])
    
    # Find all possible solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with all meetings, try with fewer meetings
        # For simplicity in this implementation, we'll use the first valid solution
        # In a real implementation, you'd implement backtracking with fewer meetings
        result = {"itinerary": []}
    else:
        # Use the first valid solution
        sol = solutions[0]
        
        # Create itinerary with proper ordering
        meetings = [
            ('Melissa', sol['melissa_start'], sol['melissa_start'] + melissa_min_duration, 'Golden Gate Park'),
            ('Nancy', sol['nancy_start'], sol['nancy_start'] + nancy_min_duration, 'Presidio'),
            ('Emily', sol['emily_start'], sol['emily_start'] + emily_min_duration, 'Richmond District')
        ]
        
        # Sort by start time
        meetings_sorted = sorted(meetings, key=lambda x: x[1])
        
        itinerary = []
        
        # Add travel from starting point to first meeting
        current_location = 'Fishermans Wharf'
        current_time = start_time
        
        for meeting in meetings_sorted:
            name, m_start, m_end, location = meeting
            
            # Add travel if needed
            if current_location != location:
                travel_time = travel_times[current_location][location]
                travel_start = current_time
                travel_end = current_time + travel_time
                
                # Ensure we don't arrive too early (wait until meeting starts)
                if travel_end < m_start:
                    # We have waiting time
                    itinerary.append({
                        "action": "travel", 
                        "location": f"From {current_location} to {location}", 
                        "person": "Travel", 
                        "start_time": minutes_to_time(travel_start), 
                        "end_time": minutes_to_time(travel_end)
                    })
                    # Add waiting period if any
                    if travel_end < m_start:
                        itinerary.append({
                            "action": "wait", 
                            "location": location, 
                            "person": "Waiting", 
                            "start_time": minutes_to_time(travel_end), 
                            "end_time": minutes_to_time(m_start)
                        })
                else:
                    # Travel directly to meeting
                    itinerary.append({
                        "action": "travel", 
                        "location": f"From {current_location} to {location}", 
                        "person": "Travel", 
                        "start_time": minutes_to_time(travel_start), 
                        "end_time": minutes_to_time(m_start)
                    })
            
            # Add the meeting
            itinerary.append({
                "action": "meet", 
                "location": location, 
                "person": name, 
                "start_time": minutes_to_time(m_start), 
                "end_time": minutes_to_time(m_end)
            })
            
            current_location = location
            current_time = m_end
        
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()