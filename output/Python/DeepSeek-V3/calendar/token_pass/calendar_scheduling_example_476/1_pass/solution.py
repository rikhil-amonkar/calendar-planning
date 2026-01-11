def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30

    # Busy times in minutes from midnight, but we'll convert from 9:00 later
    # Actually easier: store as (start_min, end_min) from 0:00
    # But for clarity, define from 9:00 as 0
    # Let's define a function to convert "HH:MM" to minutes from 9:00
    def t(x):
        return time_to_minutes(x) - work_start

    busy = {
        "Daniel": [],
        "Kathleen": [(t("14:30"), t("15:30"))],
        "Carolyn": [(t("12:00"), t("12:30")), (t("13:00"), t("13:30"))],
        "Roger": [],
        "Cheryl": [(t("09:00"), t("09:30")), (t("10:00"), t("11:30")), (t("12:30"), t("13:30")), (t("14:00"), t("17:00"))],
        "Virginia": [(t("09:30"), t("11:30")), (t("12:00"), t("12:30")), (t("13:00"), t("13:30")), (t("14:30"), t("15:30")), (t("16:00"), t("17:00"))],
        "Angela": [(t("09:30"), t("10:00")), (t("10:30"), t("11:30")), (t("12:00"), t("12:30")), (t("13:00"), t("13:30")), (t("14:00"), t("16:30"))],
    }

    # Roger's preference: not before 12:30
    roger_pref_start = t("12:30")

    # Check every possible start time from work_start to work_end - duration, step 1 minute
    # But step 30 mins for efficiency
    for start in range(roger_pref_start, work_end - work_start - duration + 1, 1):
        end = start + duration
        ok = True
        for person, blocks in busy.items():
            for s_busy, e_busy in blocks:
                if not (end <= s_busy or start >= e_busy):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            # Convert start back to HH:MM from 9:00 base
            start_abs = start + work_start
            end_abs = end + work_start
            print(f"Monday {minutes_to_time(start_abs)}:{minutes_to_time(end_abs)}")
            return

if __name__ == "__main__":
    main()