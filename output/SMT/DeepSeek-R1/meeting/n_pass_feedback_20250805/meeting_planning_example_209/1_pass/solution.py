from z3 import *

def main():
    # Define meetings with their constraints (times in minutes from 9:00 AM)
    meetings = [
        {"name": "Melissa", "location": "North Beach", "duration": 105, "min_start": 29, "max_end": 270},
        {"name": "Anthony", "location": "Chinatown", "duration": 60, "min_start": 255, "max_end": 330},
        {"name": "Rebecca", "location": "Russian Hill", "duration": 105, "min_start": 630, "max_end": 735}
    ]
    
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Russian Hill'): 4,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9
    }
    
    # Create Z3 integer variables for start times
    starts = [Int(f'start_{i}') for i in range(3)]
    ends = [Int(f'end_{i}') for i in range(3)]
    
    s = Solver()
    
    # Add constraints for each meeting: end time and availability
    for i in range(3):
        s.add(ends[i] == starts[i] + meetings[i]['duration'])
        s.add(starts[i] >= meetings[i]['min_start'])
        s.add(ends[i] <= meetings[i]['max_end'])
    
    # Define travel constraints for the fixed order: Melissa (0) -> Anthony (1) -> Rebecca (2)
    s.add(starts[0] >= travel_times[('Sunset District', meetings[0]['location'])])
    s.add(starts[1] >= ends[0] + travel_times[(meetings[0]['location'], meetings[1]['location'])])
    s.add(starts[2] >= ends[1] + travel_times[(meetings[1]['location'], meetings[2]['location'])])
    
    # Check for a feasible solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(3):
            start_val = model.eval(starts[i]).as_long()
            total_minutes = start_val
            hours = total_minutes // 60
            minutes = total_minutes % 60
            start_time = f"{hours:02d}:{minutes:02d}"
            
            end_val = start_val + meetings[i]['duration']
            hours_end = end_val // 60
            minutes_end = end_val % 60
            end_time = f"{hours_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": meetings[i]['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        
        # Sort itinerary by start time (though order is fixed)
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()