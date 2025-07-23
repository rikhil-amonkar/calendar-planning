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
    
    for i in range(n):
        solver.add(s[i] >= 0)
        solver.add(s[i] % 5 == 0)
        solver.add(s[i] + meetings[i][1] <= 779)
    
    for i in range(n):
        for j in range(i + 1, n):
            solver.add(Or(
                s[j] >= s[i] + meetings[i][1] + 10,
                s[i] >= s[j] + meetings[j][1] + 10
            ))
    
    if solver.check() == sat:
        model = solver.model()
        start_times = [model.evaluate(s[i]).as_long() for i in range(n)]
        schedule = []
        for i in range(n):
            start_minutes = start_times[i]
            total_minutes = start_minutes
            hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            start_str = f"{hours:02d}:{minutes:02d}"
            
            end_minutes = start_minutes + meetings[i][1]
            end_hours = 9 + end_minutes // 60
            end_minutes_part = end_minutes % 60
            end_str = f"{end_hours:02d}:{end_minutes_part:02d}"
            
            schedule.append((start_minutes, meetings[i][0], start_str, end_str))
        
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for _, name, start_str, end_str in schedule:
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