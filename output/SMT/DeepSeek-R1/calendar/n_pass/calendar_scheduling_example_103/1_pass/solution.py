from z3 import *

def main():
    # Convert time to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        total_minutes = (hours - 9) * 60 + minutes
        return total_minutes

    # Busy intervals for each person in minutes (since 9:00)
    diane_busy = [('9:30', '10:00'), ('14:30', '15:00')]
    jack_busy = [('13:30', '14:00'), ('14:30', '15:00')]
    eugene_busy = [('9:00', '10:00'), ('10:30', '11:30'), ('12:00', '14:30'), ('15:00', '16:30')]
    patricia_busy = [('9:30', '10:30'), ('11:00', '12:00'), ('12:30', '14:00'), ('15:00', '16:30')]

    # Convert all busy times to minutes
    def convert_intervals(intervals):
        converted = []
        for start, end in intervals:
            s_min = time_to_minutes(start)
            e_min = time_to_minutes(end)
            converted.append((s_min, e_min))
        return converted

    diane_intervals = convert_intervals(diane_busy)
    jack_intervals = convert_intervals(jack_busy)
    eugene_intervals = convert_intervals(eugene_busy)
    patricia_intervals = convert_intervals(patricia_busy)

    # Create a solver
    s = Solver()
    # S is the start time in minutes from 9:00
    S = Int('S')
    # Meeting duration is 30 minutes, and must end by 17:00 (480 minutes from 00:00, but 17:00 is 8*60=480 from 9:00)
    s.add(S >= 0)
    s.add(S <= 450)  # 450 because 450 + 30 = 480 (17:00)

    # Function to add constraints for a person's busy intervals
    def add_person_constraints(intervals):
        for (busy_start, busy_end) in intervals:
            s.add(Or(S + 30 <= busy_start, S >= busy_end))

    add_person_constraints(diane_intervals)
    add_person_constraints(jack_intervals)
    add_person_constraints(eugene_intervals)
    add_person_constraints(patricia_intervals)

    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        # Convert start_minutes back to time string
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes_part = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_part:02d}"
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()