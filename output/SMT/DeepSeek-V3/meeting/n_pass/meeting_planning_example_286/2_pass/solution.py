from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define variables for meeting start and end times (in minutes since 9:00AM)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Convert all times to minutes since 9:00AM (540 minutes since midnight)
    # Carol's availability: 10:15AM (615) to 11:45AM (705)
    carol_available_start = 615 - 540  # 75
    carol_available_end = 705 - 540    # 165

    # Rebecca's availability: 11:30AM (690) to 8:15PM (1215)
    rebecca_available_start = 690 - 540  # 150
    rebecca_available_end = 1215 - 540   # 675

    # Karen's availability: 12:45PM (765) to 3:00PM (900)
    karen_available_start = 765 - 540    # 225
    karen_available_end = 900 - 540      # 360

    # Travel times (in minutes)
    travel = {
        ('Union Square', 'Sunset District'): 26,
        ('Sunset District', 'Mission District'): 24,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Mission District'): 13,
        ('Mission District', 'Union Square'): 15,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Bayview', 'Union Square'): 17,
        ('Sunset District', 'Bayview'): 22,
        ('Bayview', 'Sunset District'): 23
    }

    # Meeting duration constraints
    s.add(carol_end - carol_start >= 30)   # Carol: min 30 mins
    s.add(rebecca_end - rebecca_start >= 120)  # Rebecca: min 120 mins
    s.add(karen_end - karen_start >= 120)  # Karen: min 120 mins

    # Availability constraints
    s.add(carol_start >= carol_available_start)
    s.add(carol_end <= carol_available_end)
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)

    # We need to model the sequence of meetings with travel times
    # There are several possible orders. We'll create variables to represent the order.
    # Let's create a variable for each possible meeting order (0=Carol first, 1=Rebecca first, etc.)
    # But for simplicity, we'll assume Carol is first (since she's available earliest)
    # Then we can choose between Rebecca or Karen next

    # Option 1: Carol -> Rebecca -> Karen
    option1 = And(
        carol_start >= travel[('Union Square', 'Sunset District')],  # Travel to Carol
        rebecca_start >= carol_end + travel[('Sunset District', 'Mission District')],
        karen_start >= rebecca_end + travel[('Mission District', 'Bayview')]
    )

    # Option 2: Carol -> Karen -> Rebecca
    option2 = And(
        carol_start >= travel[('Union Square', 'Sunset District')],  # Travel to Carol
        karen_start >= carol_end + travel[('Sunset District', 'Bayview')],
        rebecca_start >= karen_end + travel[('Bayview', 'Mission District')]
    )

    s.add(Or(option1, option2))

    # Maximize total meeting time
    total_time = (carol_end - carol_start) + (rebecca_end - rebecca_start) + (karen_end - karen_start)
    s.maximize(total_time)

    if s.check() == sat:
        m = s.model()
        def to_time(minutes):
            total = 540 + minutes
            h = total // 60
            m = total % 60
            return f"{h}:{m:02d}AM" if h < 12 else f"{h-12}:{m:02d}PM" if h < 24 else f"{h-24}:{m:02d}AM"

        print("SOLUTION:")
        print(f"Meet Carol at Sunset District from {to_time(m[carol_start].as_long())} to {to_time(m[carol_end].as_long())}")
        print(f"Meet Rebecca at Mission District from {to_time(m[rebecca_start].as_long())} to {to_time(m[rebecca_end].as_long())}")
        print(f"Meet Karen at Bayview from {to_time(m[karen_start].as_long())} to {to_time(m[karen_end].as_long())}")
        print(f"Total meeting time: {m.eval(total_time).as_long()} minutes")
    else:
        print("No valid schedule found")

solve_scheduling()