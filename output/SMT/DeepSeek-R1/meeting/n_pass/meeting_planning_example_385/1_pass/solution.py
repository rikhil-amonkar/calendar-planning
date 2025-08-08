from z3 import *
import datetime

def main():
    # Define integer variables for start times and durations
    S0, S1, S2, S3 = Ints('S0 S1 S2 S3')  # Start times for Jeffrey, John, Steven, Barbara
    D0, D1, D2, D3 = Ints('D0 D1 D2 D3')  # Durations for the meetings

    opt = Optimize()

    # Travel times in minutes
    t_NobHill_to_Presidio = 17
    t_Presidio_to_PacificHeights = 11
    t_PacificHeights_to_NorthBeach = 9
    t_NorthBeach_to_FishermansWharf = 5

    # Chain constraints for the order: Jeffrey (0) -> John (1) -> Steven (2) -> Barbara (3)
    opt.add(S0 >= t_NobHill_to_Presidio)
    opt.add(S1 >= S0 + D0 + t_Presidio_to_PacificHeights)
    opt.add(S2 >= If(S1 + D1 + t_PacificHeights_to_NorthBeach >= 270, S1 + D1 + t_PacificHeights_to_NorthBeach, 270))
    opt.add(S3 >= If(S2 + D2 + t_NorthBeach_to_FishermansWharf >= 540, S2 + D2 + t_NorthBeach_to_FishermansWharf, 540))

    # Availability window constraints
    opt.add(S0 >= 17, S0 + D0 <= 60)       # Jeffrey: 9:17 AM to 10:00 AM
    opt.add(S1 + D1 <= 270)                 # John: must end by 1:30 PM
    opt.add(S2 >= 270, S2 + D2 <= 780)      # Steven: 1:30 PM to 10:00 PM
    opt.add(S3 >= 540, S3 + D3 <= 750)      # Barbara: 6:00 PM to 9:30 PM

    # Durations must be at least 1 minute
    opt.add(D0 >= 1, D1 >= 1, D2 >= 1, D3 >= 1)

    # Maximize total meeting time
    total_duration = D0 + D1 + D2 + D3
    opt.maximize(total_duration)

    if opt.check() == sat:
        m = opt.model()
        # Extract values
        S0_val = m.eval(S0).as_long()
        D0_val = m.eval(D0).as_long()
        S1_val = m.eval(S1).as_long()
        D1_val = m.eval(D1).as_long()
        S2_val = m.eval(S2).as_long()
        D2_val = m.eval(D2).as_long()
        S3_val = m.eval(S3).as_long()
        D3_val = m.eval(D3).as_long()

        # Convert minutes to time strings (base: 9:00 AM)
        def min_to_time(minutes):
            base = datetime.datetime(2000, 1, 1, 9, 0)  # Arbitrary date, time at 9:00 AM
            new_time = base + datetime.timedelta(minutes=minutes)
            return new_time.strftime("%H:%M")

        meetings = [
            ("Jeffrey", S0_val, D0_val),
            ("John", S1_val, D1_val),
            ("Steven", S2_val, D2_val),
            ("Barbara", S3_val, D3_val)
        ]

        itinerary = []
        for person, start, duration in meetings:
            start_time = min_to_time(start)
            end_time = min_to_time(start + duration)
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_time,
                "end_time": end_time
            })

        # Output the solution in the required JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()