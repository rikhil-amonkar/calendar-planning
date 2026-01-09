from constraint import Problem
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Financial District'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Financial District'): 5,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Fisherman\'s Wharf'): 10
    }
    
    # Convert all times to minutes since midnight
    start_time = time_to_minutes('9:00')  # Arrive at Bayview
    
    # Friend constraints (in minutes since midnight)
    betty_start = time_to_minutes('19:45')  # 7:45PM
    betty_end = time_to_minutes('21:45')    # 9:45PM
    betty_min_duration = 15
    
    karen_start = time_to_minutes('8:45')   # 8:45AM
    karen_end = time_to_minutes('15:00')    # 3:00PM
    karen_min_duration = 30
    
    anthony_start = time_to_minutes('9:15') # 9:15AM
    anthony_end = time_to_minutes('21:30')  # 9:30PM
    anthony_min_duration = 105
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start times for each meeting
    problem.addVariable('karen_start', range(karen_start, karen_end - karen_min_duration + 1))
    problem.addVariable('anthony_start', range(anthony_start, anthony_end - anthony_min_duration + 1))
    problem.addVariable('betty_start', range(betty_start, betty_end - betty_min_duration + 1))
    
    def travel_constraint(k_start, a_start, b_start):
        # Calculate end times
        k_end = k_start + karen_min_duration
        a_end = a_start + anthony_min_duration
        b_end = b_start + betty_min_duration
        
        # Check if meetings overlap
        meetings = [
            ('Bayview', 'Fisherman\'s Wharf', k_start, k_end, 'Karen'),
            ('Fisherman\'s Wharf', 'Financial District', a_start, a_end, 'Anthony'),
            ('Financial District', 'Embarcadero', b_start, b_end, 'Betty')
        ]
        
        # Check travel feasibility
        current_time = start_time
        current_location = 'Bayview'
        
        for from_loc, to_loc, meet_start, meet_end, person in meetings:
            # Travel to meeting
            travel_time = travel_times.get((current_location, to_loc), float('inf'))
            if current_time + travel_time > meet_start:
                return False
            
            # Update current time and location after meeting
            current_time = meet_end
            current_location = to_loc
        
        return True
    
    problem.addConstraint(travel_constraint, ['karen_start', 'anthony_start', 'betty_start'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with all meetings, try with fewer meetings
        # Try without Betty (late meeting)
        problem_betty_removed = Problem()
        problem_betty_removed.addVariable('karen_start', range(karen_start, karen_end - karen_min_duration + 1))
        problem_betty_removed.addVariable('anthony_start', range(anthony_start, anthony_end - anthony_min_duration + 1))
        
        def travel_constraint_no_betty(k_start, a_start):
            k_end = k_start + karen_min_duration
            a_end = a_start + anthony_min_duration
            
            # Check Karen -> Anthony travel
            current_time = start_time
            current_location = 'Bayview'
            
            # Travel to Karen
            travel_time1 = travel_times.get((current_location, 'Fisherman\'s Wharf'), float('inf'))
            if current_time + travel_time1 > k_start:
                return False
            
            # After Karen meeting
            current_time = k_end
            current_location = 'Fisherman\'s Wharf'
            
            # Travel to Anthony
            travel_time2 = travel_times.get((current_location, 'Financial District'), float('inf'))
            if current_time + travel_time2 > a_start:
                return False
            
            return True
        
        problem_betty_removed.addConstraint(travel_constraint_no_betty, ['karen_start', 'anthony_start'])
        solutions = problem_betty_removed.getSolutions()
        
        if solutions:
            sol = solutions[0]
            k_start = sol['karen_start']
            a_start = sol['anthony_start']
            
            itinerary = [
                {
                    "action": "meet",
                    "location": "Fisherman's Wharf",
                    "person": "Karen",
                    "start_time": minutes_to_time(k_start),
                    "end_time": minutes_to_time(k_start + karen_min_duration)
                },
                {
                    "action": "meet",
                    "location": "Financial District",
                    "person": "Anthony",
                    "start_time": minutes_to_time(a_start),
                    "end_time": minutes_to_time(a_start + anthony_min_duration)
                }
            ]
        else:
            # Try just one meeting
            itinerary = []
            # Try Karen only
            if karen_start <= start_time + travel_times[('Bayview', 'Fisherman\'s Wharf')] <= karen_end - karen_min_duration:
                k_start = start_time + travel_times[('Bayview', 'Fisherman\'s Wharf')]
                itinerary.append({
                    "action": "meet",
                    "location": "Fisherman's Wharf",
                    "person": "Karen",
                    "start_time": minutes_to_time(k_start),
                    "end_time": minutes_to_time(k_start + karen_min_duration)
                })
            # Try Anthony only
            elif anthony_start <= start_time + travel_times[('Bayview', 'Financial District')] <= anthony_end - anthony_min_duration:
                a_start = start_time + travel_times[('Bayview', 'Financial District')]
                itinerary.append({
                    "action": "meet",
                    "location": "Financial District",
                    "person": "Anthony",
                    "start_time": minutes_to_time(a_start),
                    "end_time": minutes_to_time(a_start + anthony_min_duration)
                })
    else:
        # Found solution with all three meetings
        sol = solutions[0]
        k_start = sol['karen_start']
        a_start = sol['anthony_start']
        b_start = sol['betty_start']
        
        itinerary = [
            {
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Karen",
                "start_time": minutes_to_time(k_start),
                "end_time": minutes_to_time(k_start + karen_min_duration)
            },
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": minutes_to_time(a_start),
                "end_time": minutes_to_time(a_start + anthony_min_duration)
            },
            {
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": minutes_to_time(b_start),
                "end_time": minutes_to_time(b_start + betty_min_duration)
            }
        ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()