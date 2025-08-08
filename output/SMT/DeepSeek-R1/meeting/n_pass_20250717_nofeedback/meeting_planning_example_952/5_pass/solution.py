from z3 import *

def main():
    meetings = [
        ("Richard", 60),
        ("Elizabeth", 75),
        ("Brian", 90),
        ("Anthony", 30),
        ("Ashley", 90),
        ("Deborah", 60),
        ("Kimberly", 45),
        ("Jessica", 105)
    ]
    n = len(meetings)
    s = [Int(f's_{i}') for i in range(n)]
    
    solver = Solver()
    
    # Basic constraints for each meeting
    for i in range(n):
        # Start time must be non-negative and multiple of 5
        solver.add(s[i] >= 0)
        solver.add(s[i] % 5 == 0)
        # Meeting must end before 10:00 PM (779 minutes)
        solver.add(s[i] + meetings[i][1] <= 779)
    
    # Break constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                # Either meeting i is before j or vice versa
                before = And(s[i] + meetings[i][1] <= s[j], s[j] >= s[i] + meetings[i][1] + 10)
                after = And(s[j] + meetings[j][1] <= s[i], s[i] >= s[j] + meetings[j][1] + 10)
                solver.add(Or(before, after))
    
    if solver.check() == sat:
        model = solver.model()
        start_times = []
        for i in range(n):
            start_val = model.evaluate(s[i]).as_long()
            start_times.append((start_val, meetings[i][0], meetings[i][1]))
        
        # Sort meetings by start time
        start_times.sort(key=lambda x: x[0])
        
        itinerary = []
        for start, name, duration in start_times:
            # Convert start time to HH:MM
            total_minutes = start
            hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            start_str = f"{hours:02d}:{minutes:02d}"
            
            # Calculate end time
            end_minutes = start + duration
            end_hours = 9 + end_minutes // 60
            end_minutes_part = end_minutes % 60
            end_str = f"{end_hours:02d}:{end_minutes_part:02d}"
            
            itinerary.append({
                'action': 'meet',
                'person': name,
                'start_time': start_str,
                'end_time': end_str
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()