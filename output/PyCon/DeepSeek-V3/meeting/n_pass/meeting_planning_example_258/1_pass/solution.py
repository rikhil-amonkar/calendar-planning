import constraint
import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes
    travel_times = {
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18
    }
    
    # Convert all times to minutes since 9:00 (540 minutes from midnight)
    start_time_total = 540  # 9:00 AM in minutes
    
    # Friend constraints in minutes since midnight
    betty_start = 615  # 10:15 AM
    betty_end = 1290   # 9:30 PM
    betty_min = 45
    
    david_start = 780  # 1:00 PM
    david_end = 1215   # 8:15 PM
    david_min = 90
    
    barbara_start = 555  # 9:15 AM
    barbara_end = 1215   # 8:15 PM
    barbara_min = 120
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for meeting start times and durations
    # We'll use minutes since 9:00 AM as our time unit
    
    # Possible meeting orders (0: Betty, 1: David, 2: Barbara)
    # We'll try all permutations of meetings
    from itertools import permutations
    meeting_orders = list(permutations([0, 1, 2]))
    
    best_schedule = None
    max_meetings = 0
    
    for order in meeting_orders:
        problem = constraint.Problem()
        
        # Variables: start times for each meeting (in minutes since 9:00)
        problem.addVariable(f'start_{order[0]}', range(0, 1440))
        problem.addVariable(f'start_{order[1]}', range(0, 1440))
        problem.addVariable(f'start_{order[2]}', range(0, 1440))
        
        # Variables: durations for each meeting
        problem.addVariable(f'dur_{order[0]}', [betty_min])
        problem.addVariable(f'dur_{order[1]}', [david_min])
        problem.addVariable(f'dur_{order[2]}', [barbara_min])
        
        # Helper function to get location for a person
        def get_location(person_idx):
            if person_idx == 0:  # Betty
                return 'Presidio'
            elif person_idx == 1:  # David
                return 'Richmond District'
            else:  # Barbara
                return 'Fisherman\'s Wharf'
        
        # Helper function to get time window for a person
        def get_time_window(person_idx):
            if person_idx == 0:  # Betty
                return (betty_start, betty_end)
            elif person_idx == 1:  # David
                return (david_start, david_end)
            else:  # Barbara
                return (barbara_start, barbara_end)
        
        # Constraints for first meeting
        def first_meeting_constraint(start_0, dur_0):
            # First meeting must start after arrival + travel time
            location_0 = get_location(order[0])
            travel_time_0 = travel_times[('Embarcadero', location_0)]
            actual_start_0 = start_time_total + travel_time_0
            
            # Check if meeting fits in person's availability
            person_window_0 = get_time_window(order[0])
            end_0 = actual_start_0 + dur_0
            
            return (actual_start_0 >= person_window_0[0] and 
                    end_0 <= person_window_0[1] and
                    actual_start_0 == start_0)
        
        problem.addConstraint(first_meeting_constraint, [f'start_{order[0]}', f'dur_{order[0]}'])
        
        # Constraints for second meeting
        def second_meeting_constraint(start_0, dur_0, start_1, dur_1):
            location_0 = get_location(order[0])
            location_1 = get_location(order[1])
            
            # Travel time between locations
            travel_time = travel_times[(location_0, location_1)]
            
            # Second meeting must start after first meeting ends + travel time
            end_0 = start_0 + dur_0
            earliest_start_1 = end_0 + travel_time
            
            # Check if meeting fits in person's availability
            person_window_1 = get_time_window(order[1])
            end_1 = start_1 + dur_1
            
            return (start_1 >= earliest_start_1 and
                    start_1 >= person_window_1[0] and
                    end_1 <= person_window_1[1])
        
        problem.addConstraint(second_meeting_constraint, 
                            [f'start_{order[0]}', f'dur_{order[0]}', 
                             f'start_{order[1]}', f'dur_{order[1]}'])
        
        # Constraints for third meeting
        def third_meeting_constraint(start_1, dur_1, start_2, dur_2):
            location_1 = get_location(order[1])
            location_2 = get_location(order[2])
            
            # Travel time between locations
            travel_time = travel_times[(location_1, location_2)]
            
            # Third meeting must start after second meeting ends + travel time
            end_1 = start_1 + dur_1
            earliest_start_2 = end_1 + travel_time
            
            # Check if meeting fits in person's availability
            person_window_2 = get_time_window(order[2])
            end_2 = start_2 + dur_2
            
            return (start_2 >= earliest_start_2 and
                    start_2 >= person_window_2[0] and
                    end_2 <= person_window_2[1])
        
        problem.addConstraint(third_meeting_constraint, 
                            [f'start_{order[1]}', f'dur_{order[1]}', 
                             f'start_{order[2]}', f'dur_{order[2]}'])
        
        # Find solutions
        solutions = problem.getSolutions()
        
        if solutions:
            # Count how many meetings we can have
            meetings_count = 3
            current_best = max_meetings
            
            if meetings_count > max_meetings:
                max_meetings = meetings_count
                # Take the first valid solution
                solution = solutions[0]
                
                # Build itinerary
                itinerary = []
                
                # Add meetings in order
                for i, person_idx in enumerate(order):
                    start_minutes = solution[f'start_{person_idx}']
                    duration = solution[f'dur_{person_idx}']
                    end_minutes = start_minutes + duration
                    
                    # Convert to time strings
                    start_time = minutes_to_time(start_minutes)
                    end_time = minutes_to_time(end_minutes)
                    
                    if person_idx == 0:  # Betty
                        itinerary.append({
                            "action": "meet",
                            "location": "Presidio",
                            "person": "Betty",
                            "start_time": start_time,
                            "end_time": end_time
                        })
                    elif person_idx == 1:  # David
                        itinerary.append({
                            "action": "meet",
                            "location": "Richmond District",
                            "person": "David",
                            "start_time": start_time,
                            "end_time": end_time
                        })
                    else:  # Barbara
                        itinerary.append({
                            "action": "meet",
                            "location": "Fisherman's Wharf",
                            "person": "Barbara",
                            "start_time": start_time,
                            "end_time": end_time
                        })
                
                best_schedule = itinerary
    
    # If we couldn't schedule all 3, try scheduling 2 meetings
    if best_schedule is None:
        # Try all combinations of 2 meetings
        from itertools import combinations
        for combo in combinations([0, 1, 2], 2):
            for order in permutations(combo):
                problem = constraint.Problem()
                
                # Variables for the 2 meetings
                problem.addVariable(f'start_{order[0]}', range(0, 1440))
                problem.addVariable(f'start_{order[1]}', range(0, 1440))
                
                problem.addVariable(f'dur_{order[0]}', [getattr(locals(), [f'{name}_min' for name in ['betty', 'david', 'barbara']][order[0]])])
                problem.addVariable(f'dur_{order[1]}', [getattr(locals(), [f'{name}_min' for name in ['betty', 'david', 'barbara']][order[1]])])
                
                # First meeting constraint
                def first_meeting_2_constraint(start_0, dur_0):
                    location_0 = get_location(order[0])
                    travel_time_0 = travel_times[('Embarcadero', location_0)]
                    actual_start_0 = start_time_total + travel_time_0
                    
                    person_window_0 = get_time_window(order[0])
                    end_0 = actual_start_0 + dur_0
                    
                    return (actual_start_0 >= person_window_0[0] and 
                            end_0 <= person_window_0[1] and
                            actual_start_0 == start_0)
                
                problem.addConstraint(first_meeting_2_constraint, [f'start_{order[0]}', f'dur_{order[0]}'])
                
                # Second meeting constraint
                def second_meeting_2_constraint(start_0, dur_0, start_1, dur_1):
                    location_0 = get_location(order[0])
                    location_1 = get_location(order[1])
                    
                    travel_time = travel_times[(location_0, location_1)]
                    
                    end_0 = start_0 + dur_0
                    earliest_start_1 = end_0 + travel_time
                    
                    person_window_1 = get_time_window(order[1])
                    end_1 = start_1 + dur_1
                    
                    return (start_1 >= earliest_start_1 and
                            start_1 >= person_window_1[0] and
                            end_1 <= person_window_1[1])
                
                problem.addConstraint(second_meeting_2_constraint, 
                                    [f'start_{order[0]}', f'dur_{order[0]}', 
                                     f'start_{order[1]}', f'dur_{order[1]}'])
                
                solutions = problem.getSolutions()
                
                if solutions and 2 > max_meetings:
                    max_meetings = 2
                    solution = solutions[0]
                    
                    itinerary = []
                    
                    for i, person_idx in enumerate(order):
                        start_minutes = solution[f'start_{person_idx}']
                        duration = solution[f'dur_{person_idx}']
                        end_minutes = start_minutes + duration
                        
                        start_time = minutes_to_time(start_minutes)
                        end_time = minutes_to_time(end_minutes)
                        
                        if person_idx == 0:  # Betty
                            itinerary.append({
                                "action": "meet",
                                "location": "Presidio",
                                "person": "Betty",
                                "start_time": start_time,
                                "end_time": end_time
                            })
                        elif person_idx == 1:  # David
                            itinerary.append({
                                "action": "meet",
                                "location": "Richmond District",
                                "person": "David",
                                "start_time": start_time,
                                "end_time": end_time
                            })
                        else:  # Barbara
                            itinerary.append({
                                "action": "meet",
                                "location": "Fisherman's Wharf",
                                "person": "Barbara",
                                "start_time": start_time,
                                "end_time": end_time
                            })
                    
                    best_schedule = itinerary
    
    # Output result
    if best_schedule:
        result = {"itinerary": best_schedule}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result, indent=2))

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string in 24-hour format"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()