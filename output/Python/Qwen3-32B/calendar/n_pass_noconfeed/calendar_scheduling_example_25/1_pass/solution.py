def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_slot_free(busy_intervals, slot_start, slot_end):
    for b_start, b_end in busy_intervals:
        if slot_end <= b_start or slot_start >= b_end:
            continue
        else:
            return False
    return True

def main():
    # Define busy intervals in minutes since midnight
    anthony_busy = [(9*60 + 30, 9*60 + 60), (12*60, 13*60), (16*60, 16*60 + 30)]
    pamela_busy = [(9*60 + 30, 9*60 + 60), (16*60 + 30, 17*60)]
    zachary_busy = [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)]
    
    # Work hours are 9:00 to 17:00 (540 to 1020)
    # Pamela's constraint: end by 14:30 (870 minutes). So start must be <= 810.
    for start_minutes in range(540, 810 + 1):
        end_minutes = start_minutes + 60
        anthony_ok = is_slot_free(anthony_busy, start_minutes, end_minutes)
        pamela_ok = is_slot_free(pamela_busy, start_minutes, end_minutes)
        zachary_ok = is_slot_free(zachary_busy, start_minutes, end_minutes)
        if anthony_ok and pamela_ok and zachary_ok:
            start_str = minutes_to_time(start_minutes)
            end_str = minutes_to_time(end_minutes)
            print(f"{{{start_str}:{end_str}}} Monday")
            return

main()