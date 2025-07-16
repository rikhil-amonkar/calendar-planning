from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Kevin at Alamo Square
    kevin_start = Int('kevin_start')
    kevin_end = Int('kevin_end')
    # Kimberly at Russian Hill
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    # Joseph at Presidio
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    # Thomas at Financial District
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Define arrival time at Sunset District (9:00 AM in minutes since midnight)
    arrival_time = 9 * 60  # 9:00 AM

    # Convert all times to minutes since midnight for easier calculations
    # Kevin's availability: 8:15 AM to 9:30 PM (495 to 1410 minutes)
    kevin_available_start = 8 * 60 + 15  # 8:15 AM
    kevin_available_end = 21 * 60 + 30   # 9:30 PM
    # Kimberly's availability: 8:45 AM to 12:30 PM (525 to 750 minutes)
    kimberly_available_start = 8 * 60 + 45  # 8:45 AM
    kimberly_available_end = 12 * 60 + 30   # 12:30 PM
    # Joseph's availability: 6:30 PM to 7:15 PM (1170 to 1275 minutes)
    joseph_available_start = 18 * 60 + 30  # 6:30 PM
    joseph_available_end = 19 * 60 + 15     # 7:15 PM
    # Thomas's availability: 7:00 PM to 9:45 PM (1260 to 1425 minutes)
    thomas_available_start = 19 * 60  # 7:00 PM
    thomas_available_end = 21 * 60 + 45  # 9:45 PM

    # Meeting duration constraints
    kevin_duration = 75
    kimberly_duration = 30
    joseph_duration = 45
    thomas_duration = 45

    # Add constraints for each meeting's start and end times within availability
    s.add(kevin_start >= kevin_available_start)
    s.add(kevin_end <= kevin_available_end)
    s.add(kevin_end == kevin_start + kevin_duration)

    s.add(kimberly_start >= kimberly_available_start)
    s.add(kimberly_end <= kimberly_available_end)
    s.add(kimberly_end == kimberly_start + kimberly_duration)

    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)
    s.add(joseph_end == joseph_start + joseph_duration)

    s.add(thomas_start >= thomas_available_start)
    s.add(thomas_end <= thomas_available_end)
    s.add(thomas_end == thomas_start + thomas_duration)

    # Define travel times (in minutes)
    # From Sunset District to Alamo Square: 17
    sunset_to_alamo = 17
    # From Alamo Square to Russian Hill: 13
    alamo_to_russian = 13
    # From Russian Hill to Presidio: 14
    russian_to_presidio = 14
    # From Presidio to Financial District: 23
    presidio_to_financial = 23

    # Define possible sequences of meetings
    # We'll try to meet Kevin first, then Kimberly, then Joseph, then Thomas
    # This is one possible sequence; other sequences can be tried if this fails

    # Start at Sunset District at 9:00 AM (arrival_time)
    # Travel to Alamo Square to meet Kevin
    s.add(kevin_start >= arrival_time + sunset_to_alamo)
    # Travel from Alamo Square to Russian Hill to meet Kimberly
    s.add(kimberly_start >= kevin_end + alamo_to_russian)
    # Travel from Russian Hill to Presidio to meet Joseph
    s.add(joseph_start >= kimberly_end + russian_to_presidio)
    # Travel from Presidio to Financial District to meet Thomas
    s.add(thomas_start >= joseph_end + presidio_to_financial)

    # Check if all meetings can be scheduled in this sequence
    if s.check() == sat:
        m = s.model()
        # Convert times back to readable format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        kevin_start_time = minutes_to_time(m[kevin_start].as_long())
        kimberly_start_time = minutes_to_time(m[kimberly_start].as_long())
        joseph_start_time = minutes_to_time(m[joseph_start].as_long())
        thomas_start_time = minutes_to_time(m[thomas_start].as_long())

        print("SOLUTION:")
        print(f"Meet Kevin at Alamo Square from {kevin_start_time} to {minutes_to_time(m[kevin_end].as_long())}")
        print(f"Meet Kimberly at Russian Hill from {kimberly_start_time} to {minutes_to_time(m[kimberly_end].as_long())}")
        print(f"Meet Joseph at Presidio from {joseph_start_time} to {minutes_to_time(m[joseph_end].as_long())}")
        print(f"Meet Thomas at Financial District from {thomas_start_time} to {minutes_to_time(m[thomas_end].as_long())}")
    else:
        print("No valid schedule found.")

solve_scheduling()