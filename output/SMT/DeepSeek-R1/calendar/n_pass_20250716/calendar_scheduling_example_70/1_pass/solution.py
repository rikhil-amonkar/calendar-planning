from z3 import *

def main():
    # Define the start and end of the work day in minutes from 9:00
    work_start = 0    # 9:00
    work_end = 480    # 17:00 (8 hours * 60 minutes)
    meeting_duration = 30

    # The variable for the meeting start time (in minutes from 9:00)
    start = Int('start')

    # Create an optimizer
    s = Optimize()
    s.add(start >= work_start, start <= work_end - meeting_duration)

    # Define busy intervals for each participant
    # Denise: two intervals (in minutes from 9:00)
    denise_busy = [(180, 210), (390, 420)]
    # Natalie: four intervals
    natalie_busy = [(0, 150), (180, 240), (300, 330), (360, 480)]

    # For Denise: for each busy interval, meeting must not overlap
    for interval in denise_busy:
        a, b = interval
        s.add(Or(start + meeting_duration <= a, start >= b))

    # For Natalie
    for interval in natalie_busy:
        a, b = interval
        s.add(Or(start + meeting_duration <= a, start >= b))

    # Angela has no constraints, so nothing to add

    # We want the earliest time, so minimize start
    s.minimize(start)

    # Check the model
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        # Convert to time string
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        # Format the time without leading zero for hour, but with two digits for minutes if needed.
        start_time = f"{9+hours}:{minutes:02d}"

        end_val = start_val + meeting_duration
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_time = f"{9+end_hours}:{end_minutes:02d}"

        # Since the day is Monday
        print(f"Day: Monday, Start: {start_time}, End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()