import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Embarcadero'): 6,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Pacific Heights'): 11
    }
    
    # Convert all times to minutes since 9:00 AM
    start_of_day = datetime.strptime("9:00", "%H:%M")
    
    # Convert constraint times to minutes since start
    karen_start = (datetime.strptime("18:45", "%H:%M") - start_of_day).total_seconds() // 60
    karen_end = (datetime.strptime("20:15", "%H:%M") - start_of_day).total_seconds() // 60
    mark_start = (datetime.strptime("13:00", "%H:%M") - start_of_day).total_seconds() // 60
    mark_end = (datetime.strptime("17:45", "%H:%M") - start_of_day).total_seconds() // 60
    
    # Meeting duration requirements in minutes
    karen_min_duration = 90
    mark_min_duration = 120
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting
    # karen_start_time, karen_end_time, mark_start_time, mark_end_time
    problem.addVariable('karen_start', range(int(karen_start), int(karen_end - karen_min_duration + 1)))
    problem.addVariable('mark_start', range(int(mark_start), int(mark_end - mark_min_duration + 1)))
    
    # Calculate end times based on start times and durations
    def calculate_end_times(k_start, m_start):
        k_end = k_start + karen_min_duration
        m_end = m_start + mark_min_duration
        return k_end, m_end
    
    # Constraints
    def meeting_constraint(k_start, m_start):
        k_end, m_end = calculate_end_times(k_start, m_start)
        
        # Check if meetings fit within availability windows
        if k_end > karen_end or m_end > mark_end:
            return False
        
        # Check travel time constraints for different meeting orders
        # Option 1: Meet Mark first, then Karen
        if m_end <= k_start:
            travel_time = travel_times[('Embarcadero', 'Pacific Heights')]
            if m_end + travel_time <= k_start:
                return True
        
        # Option 2: Meet Karen first, then Mark  
        if k_end <= m_start:
            travel_time = travel_times[('Pacific Heights', 'Embarcadero')]
            if k_end + travel_time <= m_start:
                return True
        
        return False
    
    problem.addConstraint(meeting_constraint, ['karen_start', 'mark_start'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with minimum durations, try to find any feasible schedule
        problem = constraint.Problem()
        # Try with reduced durations
        karen_reduced = 60
        mark_reduced = 60
        
        problem.addVariable('karen_start', range(int(karen_start), int(karen_end - karen_reduced + 1)))
        problem.addVariable('mark_start', range(int(mark_start), int(mark_end - mark_reduced + 1)))
        
        def reduced_constraint(k_start, m_start):
            k_end = k_start + karen_reduced
            m_end = m_start + mark_reduced
            
            if k_end > karen_end or m_end > mark_end:
                return False
            
            if m_end <= k_start:
                travel_time = travel_times[('Embarcadero', 'Pacific Heights')]
                if m_end + travel_time <= k_start:
                    return True
            
            if k_end <= m_start:
                travel_time = travel_times[('Pacific Heights', 'Embarcadero')]
                if k_end + travel_time <= m_start:
                    return True
            
            return False
        
        problem.addConstraint(reduced_constraint, ['karen_start', 'mark_start'])
        solutions = problem.getSolutions()
        
        if not solutions:
            # Return empty itinerary if no solution found
            result = {"itinerary": []}
            print(json.dumps(result, indent=2))
            return
    
    # Use the first valid solution
    solution = solutions[0]
    k_start = solution['karen_start']
    m_start = solution['mark_start']
    
    # Calculate actual meeting times
    k_end = k_start + karen_min_duration
    m_end = m_start + mark_min_duration
    
    # Determine meeting order based on start times
    if m_start > k_end:
        # Meet Karen first, then Mark
        first_meeting = {
            "action": "meet",
            "location": "Pacific Heights", 
            "person": "Karen",
            "start_time": (start_of_day + timedelta(minutes=k_start)).strftime("%H:%M"),
            "end_time": (start_of_day + timedelta(minutes=k_end)).strftime("%H:%M")
        }
        second_meeting = {
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": (start_of_day + timedelta(minutes=m_start)).strftime("%H:%M"),
            "end_time": (start_of_day + timedelta(minutes=m_end)).strftime("%H:%M")
        }
        itinerary = [first_meeting, second_meeting]
    else:
        # Meet Mark first, then Karen
        first_meeting = {
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark", 
            "start_time": (start_of_day + timedelta(minutes=m_start)).strftime("%H:%M"),
            "end_time": (start_of_day + timedelta(minutes=m_end)).strftime("%H:%M")
        }
        second_meeting = {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Karen",
            "start_time": (start_of_day + timedelta(minutes=k_start)).strftime("%H:%M"),
            "end_time": (start_of_day + timedelta(minutes=k_end)).strftime("%H:%M")
        }
        itinerary = [first_meeting, second_meeting]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()