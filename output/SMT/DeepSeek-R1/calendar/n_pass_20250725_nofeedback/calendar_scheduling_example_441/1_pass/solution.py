from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return (hours - 9) * 60 + minutes

def main():
    participants = {
        "Joan": ["11:30 to 12:00", "14:30 to 15:00"],
        "Megan": ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"],
        "Austin": [],
        "Betty": ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"],
        "Judith": ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"],
        "Terry": ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"],
        "Kathryn": ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"]
    }
    
    busy_intervals = []
    for person, schedules in participants.items():
        person_intervals = []
        for s in schedules:
            parts = s.split(' to ')
            start_str = parts[0].strip()
            end_str = parts[1].strip()
            start_minutes = time_to_minutes(start_str)
            end_minutes = time_to_minutes(end_str)
            person_intervals.append((start_minutes, end_minutes))
        busy_intervals.append(person_intervals)
    
    S = Int('S')
    solver = Solver()
    solver.add(S >= 0)
    solver.add(S <= 450)  # 480 - 30 = 450
    
    for intervals in busy_intervals:
        for (A, B) in intervals:
            solver.add(Or(S + 30 <= A, S >= B))
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[S].as_long()
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes_part = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_part:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()