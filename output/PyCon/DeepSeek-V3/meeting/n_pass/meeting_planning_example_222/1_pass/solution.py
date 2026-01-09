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
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Bayview'): 22,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Fisherman\'s Wharf'): 25
    }
    
    # Convert all times to minutes since midnight
    start_time_nob_hill = time_to_minutes('9:00')
    
    # Friend constraints (in minutes since midnight)
    helen_start = time_to_minutes('7:00')
    helen_end = time_to_minutes('16:45')  # 4:45 PM
    helen_min_duration = 120
    
    kimberly_start = time_to_minutes('16:30')  # 4:30 PM
    kimberly_end = time_to_minutes('21:00')    # 9:00 PM
    kimberly_min_duration = 45
    
    patricia_start = time_to_minutes('18:00')  # 6:00 PM
    patricia_end = time_to_minutes('21:15')    # 9:15 PM
    patricia_min_duration = 120
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start times for each meeting
    # We'll use minutes since midnight
    helen_start_var = 'helen_start'
    kimberly_start_var = 'kimberly_start'
    patricia_start_var = 'patricia_start'
    
    # Add variables with their domains
    problem.addVariable(helen_start_var, range(helen_start, helen_end - helen_min_duration + 1))
    problem.addVariable(kimberly_start_var, range(kimberly_start, kimberly_end - kimberly_min_duration + 1))
    problem.addVariable(patricia_start_var, range(patricia_start, patricia_end - patricia_min_duration + 1))
    
    # Helper function to check if we can travel between meetings
    def can_travel_between(first_end, second_start, from_loc, to_loc):
        travel_time = travel_times.get((from_loc, to_loc), float('inf'))
        return second_start >= first_end + travel_time
    
    # Constraints for meeting Helen first
    def helen_first_constraint(h_start, k_start, p_start):
        h_end = h_start + helen_min_duration
        k_end = k_start + kimberly_min_duration
        p_end = p_start + patricia_min_duration
        
        # Check if we can travel from Nob Hill to North Beach to meet Helen
        if h_start < start_time_nob_hill + travel_times[('Nob Hill', 'North Beach')]:
            return False
        
        # Try Helen -> Kimberly -> Patricia
        if (can_travel_between(h_end, k_start, 'North Beach', 'Fisherman\'s Wharf') and
            can_travel_between(k_end, p_start, 'Fisherman\'s Wharf', 'Bayview')):
            return True
        
        # Try Helen -> Patricia -> Kimberly
        if (can_travel_between(h_end, p_start, 'North Beach', 'Bayview') and
            can_travel_between(p_end, k_start, 'Bayview', 'Fisherman\'s Wharf')):
            return True
        
        return False
    
    # Constraints for meeting Kimberly first
    def kimberly_first_constraint(h_start, k_start, p_start):
        h_end = h_start + helen_min_duration
        k_end = k_start + kimberly_min_duration
        p_end = p_start + patricia_min_duration
        
        # Check if we can travel from Nob Hill to Fisherman's Wharf to meet Kimberly
        if k_start < start_time_nob_hill + travel_times[('Nob Hill', 'Fisherman\'s Wharf')]:
            return False
        
        # Try Kimberly -> Helen -> Patricia
        if (can_travel_between(k_end, h_start, 'Fisherman\'s Wharf', 'North Beach') and
            can_travel_between(h_end, p_start, 'North Beach', 'Bayview')):
            return True
        
        # Try Kimberly -> Patricia -> Helen
        if (can_travel_between(k_end, p_start, 'Fisherman\'s Wharf', 'Bayview') and
            can_travel_between(p_end, h_start, 'Bayview', 'North Beach')):
            return True
        
        return False
    
    # Constraints for meeting Patricia first
    def patricia_first_constraint(h_start, k_start, p_start):
        h_end = h_start + helen_min_duration
        k_end = k_start + kimberly_min_duration
        p_end = p_start + patricia_min_duration
        
        # Check if we can travel from Nob Hill to Bayview to meet Patricia
        if p_start < start_time_nob_hill + travel_times[('Nob Hill', 'Bayview')]:
            return False
        
        # Try Patricia -> Helen -> Kimberly
        if (can_travel_between(p_end, h_start, 'Bayview', 'North Beach') and
            can_travel_between(h_end, k_start, 'North Beach', 'Fisherman\'s Wharf')):
            return True
        
        # Try Patricia -> Kimberly -> Helen
        if (can_travel_between(p_end, k_start, 'Bayview', 'Fisherman\'s Wharf') and
            can_travel_between(k_end, h_start, 'Fisherman\'s Wharf', 'North Beach')):
            return True
        
        return False
    
    # Add the ordering constraints
    problem.addConstraint(helen_first_constraint, [helen_start_var, kimberly_start_var, patricia_start_var])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try Kimberly first if Helen first doesn't work
        problem = Problem()
        problem.addVariable(helen_start_var, range(helen_start, helen_end - helen_min_duration + 1))
        problem.addVariable(kimberly_start_var, range(kimberly_start, kimberly_end - kimberly_min_duration + 1))
        problem.addVariable(patricia_start_var, range(patricia_start, patricia_end - patricia_min_duration + 1))
        problem.addConstraint(kimberly_first_constraint, [helen_start_var, kimberly_start_var, patricia_start_var])
        solutions = problem.getSolutions()
    
    if not solutions:
        # Try Patricia first if others don't work
        problem = Problem()
        problem.addVariable(helen_start_var, range(helen_start, helen_end - helen_min_duration + 1))
        problem.addVariable(kimberly_start_var, range(kimberly_start, kimberly_end - kimberly_min_duration + 1))
        problem.addVariable(patricia_start_var, range(patricia_start, patricia_end - patricia_min_duration + 1))
        problem.addConstraint(patricia_first_constraint, [helen_start_var, kimberly_start_var, patricia_start_var])
        solutions = problem.getSolutions()
    
    if solutions:
        # Use the first valid solution
        solution = solutions[0]
        helen_start_time = solution[helen_start_var]
        kimberly_start_time = solution[kimberly_start_var]
        patricia_start_time = solution[patricia_start_var]
        
        # Determine the actual order based on start times
        meetings = [
            {'person': 'Helen', 'location': 'North Beach', 'start': helen_start_time, 'end': helen_start_time + helen_min_duration},
            {'person': 'Kimberly', 'location': 'Fisherman\'s Wharf', 'start': kimberly_start_time, 'end': kimberly_start_time + kimberly_min_duration},
            {'person': 'Patricia', 'location': 'Bayview', 'start': patricia_start_time, 'end': patricia_start_time + patricia_min_duration}
        ]
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Build itinerary
        itinerary = []
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Fallback: try to meet at least two people
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()