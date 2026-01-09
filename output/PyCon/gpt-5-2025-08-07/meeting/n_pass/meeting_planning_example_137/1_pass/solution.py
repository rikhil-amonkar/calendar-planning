import constraint
import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23
    }
    
    # Convert times to minutes since 9:00 AM (540 minutes)
    kenneth_start = 12 * 60  # 12:00 PM
    kenneth_end = 15 * 60    # 3:00 PM
    barbara_start = 8 * 60 + 15  # 8:15 AM
    barbara_end = 19 * 60        # 7:00 PM
    
    kenneth_min_duration = 90  # minutes
    barbara_min_duration = 45  # minutes
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Define variables for meeting start times and durations
    # We'll plan to meet Kenneth first, then Barbara
    # Variables: kenneth_start_time, kenneth_duration, barbara_start_time, barbara_duration
    
    # Kenneth can only be met between 12:00 and 3:00 PM
    problem.addVariable('kenneth_start_time', range(kenneth_start, kenneth_end - kenneth_min_duration + 1))
    problem.addVariable('kenneth_duration', range(kenneth_min_duration, kenneth_end - kenneth_start + 1))
    
    # Barbara can only be met between 8:15 AM and 7:00 PM
    problem.addVariable('barbara_start_time', range(barbara_start, barbara_end - barbara_min_duration + 1))
    problem.addVariable('barbara_duration', range(barbara_min_duration, barbara_end - barbara_start + 1))
    
    # Add constraints
    def travel_and_time_constraint(k_start, k_dur, b_start, b_dur):
        k_end = k_start + k_dur
        b_end = b_start + b_dur
        
        # Check if Kenneth meeting fits within his availability
        if k_start < kenneth_start or k_end > kenneth_end:
            return False
        
        # Check if Barbara meeting fits within her availability
        if b_start < barbara_start or b_end > barbara_end:
            return False
        
        # We start at Financial District at 9:00 AM
        current_time = 9 * 60  # 9:00 AM in minutes
        
        # Option 1: Meet Kenneth first, then Barbara
        # Travel from Financial District to Chinatown
        travel_to_kenneth = travel_times[('Financial District', 'Chinatown')]
        arrival_at_kenneth = current_time + travel_to_kenneth
        
        # Can we meet Kenneth at the planned time?
        if arrival_at_kenneth > k_start:
            return False
        
        # Meet Kenneth
        k_end_time = k_start + k_dur
        
        # Travel from Chinatown to Golden Gate Park
        travel_to_barbara = travel_times[('Chinatown', 'Golden Gate Park')]
        arrival_at_barbara = k_end_time + travel_to_barbara
        
        # Can we meet Barbara at the planned time?
        if arrival_at_barbara > b_start:
            return False
        
        # Check if Barbara meeting ends within her availability
        if b_start + b_dur > barbara_end:
            return False
        
        return True
    
    problem.addConstraint(travel_and_time_constraint, 
                         ['kenneth_start_time', 'kenneth_duration', 
                          'barbara_start_time', 'barbara_duration'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try alternative order: Barbara first, then Kenneth
        problem = constraint.Problem()
        
        # Kenneth variables
        problem.addVariable('kenneth_start_time', range(kenneth_start, kenneth_end - kenneth_min_duration + 1))
        problem.addVariable('kenneth_duration', range(kenneth_min_duration, kenneth_end - kenneth_start + 1))
        
        # Barbara variables  
        problem.addVariable('barbara_start_time', range(barbara_start, barbara_end - barbara_min_duration + 1))
        problem.addVariable('barbara_duration', range(barbara_min_duration, barbara_end - barbara_start + 1))
        
        def alternative_travel_constraint(k_start, k_dur, b_start, b_dur):
            k_end = k_start + k_dur
            b_end = b_start + b_dur
            
            # Check availabilities
            if k_start < kenneth_start or k_end > kenneth_end:
                return False
            if b_start < barbara_start or b_end > barbara_end:
                return False
            
            # Start at Financial District at 9:00 AM
            current_time = 9 * 60
            
            # Meet Barbara first, then Kenneth
            # Travel from Financial District to Golden Gate Park
            travel_to_barbara = travel_times[('Financial District', 'Golden Gate Park')]
            arrival_at_barbara = current_time + travel_to_barbara
            
            if arrival_at_barbara > b_start:
                return False
            
            # Meet Barbara
            b_end_time = b_start + b_dur
            
            # Travel from Golden Gate Park to Chinatown
            travel_to_kenneth = travel_times[('Golden Gate Park', 'Chinatown')]
            arrival_at_kenneth = b_end_time + travel_to_kenneth
            
            if arrival_at_kenneth > k_start:
                return False
            
            if k_start + k_dur > kenneth_end:
                return False
            
            return True
        
        problem.addConstraint(alternative_travel_constraint,
                            ['kenneth_start_time', 'kenneth_duration',
                             'barbara_start_time', 'barbara_duration'])
        
        solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with both meetings, try to meet at least one person
        # This is a fallback - meet the person with more available time first
        itinerary = []
        
        # Try to meet Barbara (she has longer availability)
        barbara_meeting_start = max(9 * 60 + travel_times[('Financial District', 'Golden Gate Park')], barbara_start)
        barbara_meeting_end = min(barbara_meeting_start + barbara_min_duration, barbara_end)
        
        if barbara_meeting_end <= barbara_end and barbara_meeting_start >= 9 * 60:
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park", 
                "person": "Barbara",
                "start_time": format_time(barbara_meeting_start),
                "end_time": format_time(barbara_meeting_end)
            })
        
        # Try to meet Kenneth if time permits after Barbara
        if itinerary:
            last_meeting_end = barbara_meeting_end
            travel_to_kenneth = travel_times[('Golden Gate Park', 'Chinatown')]
            kenneth_arrival = last_meeting_end + travel_to_kenneth
            
            if kenneth_arrival <= kenneth_end - kenneth_min_duration:
                kenneth_meeting_start = max(kenneth_arrival, kenneth_start)
                kenneth_meeting_end = kenneth_meeting_start + kenneth_min_duration
                
                if kenneth_meeting_end <= kenneth_end:
                    itinerary.append({
                        "action": "meet",
                        "location": "Chinatown",
                        "person": "Kenneth", 
                        "start_time": format_time(kenneth_meeting_start),
                        "end_time": format_time(kenneth_meeting_end)
                    })
        else:
            # If couldn't meet Barbara, try to meet Kenneth
            kenneth_meeting_start = max(9 * 60 + travel_times[('Financial District', 'Chinatown')], kenneth_start)
            kenneth_meeting_end = min(kenneth_meeting_start + kenneth_min_duration, kenneth_end)
            
            if kenneth_meeting_end <= kenneth_end and kenneth_meeting_start >= 9 * 60:
                itinerary.append({
                    "action": "meet",
                    "location": "Chinatown",
                    "person": "Kenneth",
                    "start_time": format_time(kenneth_meeting_start),
                    "end_time": format_time(kenneth_meeting_end)
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return
    
    # Find the optimal solution (maximize total meeting time)
    best_solution = None
    max_total_time = -1
    
    for solution in solutions:
        total_time = solution['kenneth_duration'] + solution['barbara_duration']
        if total_time > max_total_time:
            max_total_time = total_time
            best_solution = solution
    
    # Build itinerary
    itinerary = []
    
    # Determine meeting order based on start times
    k_start = best_solution['kenneth_start_time']
    b_start = best_solution['barbara_start_time']
    
    if k_start < b_start:
        # Meet Kenneth first
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth",
            "start_time": format_time(k_start),
            "end_time": format_time(k_start + best_solution['kenneth_duration'])
        })
        itinerary.append({
            "action": "meet", 
            "location": "Golden Gate Park",
            "person": "Barbara",
            "start_time": format_time(b_start),
            "end_time": format_time(b_start + best_solution['barbara_duration'])
        })
    else:
        # Meet Barbara first
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park", 
            "person": "Barbara",
            "start_time": format_time(b_start),
            "end_time": format_time(b_start + best_solution['barbara_duration'])
        })
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth", 
            "start_time": format_time(k_start),
            "end_time": format_time(k_start + best_solution['kenneth_duration'])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

def format_time(minutes):
    """Convert minutes since midnight to time string in format 'H:MM'"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()