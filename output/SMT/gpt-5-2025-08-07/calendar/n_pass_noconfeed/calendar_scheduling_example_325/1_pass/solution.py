from z3 import *

def t(h, m):
    return h * 60 + m

def add_no_overlap(slv, start_var, dur, intervals):
    for (bs, be) in intervals:
        slv.add(Or(start_var + dur <= bs, start_var >= be))

# Problem setup
day = "Monday"
work_start = t(9, 0)
work_end = t(17, 0)
duration = 30  # minutes

# Participants' busy times on Monday (inclusive start, exclusive end)
jose_busy = [(t(11, 0), t(11, 30)), (t(12, 30), t(13, 0))]
keith_busy = [(t(14, 0), t(14, 30)), (t(15, 0), t(15, 30))]
logan_busy = [(t(9, 0), t(10, 0)), (t(12, 0), t(12, 30)), (t(15, 0), t(15, 30))]
megan_busy = [(t(9, 0), t(10, 30)), (t(11, 0), t(12, 0)), (t(13, 0), t(13, 30)), (t(14, 30), t(16, 30))]
gary_busy = [(t(9, 0), t(9, 30)), (t(10, 0), t(10, 30)), (t(11, 30), t(13, 0)), (t(13, 30), t(14, 0)), (t(14, 30), t(16, 30))]
bobby_busy = [(t(11, 0), t(11, 30)), (t(12, 0), t(12, 30)), (t(13, 0), t(16, 0))]

# Jose does not want to meet after 15:30 => meeting must end by 15:30
jose_end_pref = t(15, 30)

opt = Optimize()
start = Int('start')

# Core constraints
opt.add(start >= work_start)
opt.add(start + duration <= work_end)
# Align meetings to 30-minute grid to match typical calendar slots
opt.add(start % 30 == 0)
# Jose preference: end no later than 15:30
opt.add(start + duration <= jose_end_pref)

# No-overlap constraints
add_no_overlap(opt, start, duration, jose_busy)
add_no_overlap(opt, start, duration, keith_busy)
add_no_overlap(opt, start, duration, logan_busy)
add_no_overlap(opt, start, duration, megan_busy)
add_no_overlap(opt, start, duration, gary_busy)
add_no_overlap(opt, start, duration, bobby_busy)

# Prefer earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s_min = m[start].as_long()
    e_min = s_min + duration
    sh, sm = divmod(s_min, 60)
    eh, em = divmod(e_min, 60)
    print(f"{day} {{{sh:02d}:{sm:02d}:{eh:02d}:{em:02d}}}")
else:
    print("No feasible time found.")