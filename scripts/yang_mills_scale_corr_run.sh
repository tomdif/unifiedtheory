#!/bin/zsh
# Runs the gauge probe, pausing it whenever 4 or more other heavy Lean or Python jobs are active on the machine.
cd ~/unifiedtheory
guarded() {
  nice -n 15 python3 scripts/yang_mills_scale_corr_gauge.py "$@" &
  local pid=$!
  while kill -0 $pid 2>/dev/null; do
    local n=$(( $(pgrep -x lean | wc -l) + $(pgrep -f 'python3 scripts/yang_mills' | grep -vx $pid | wc -l) ))
    if [ $n -ge 4 ]; then kill -STOP $pid; else kill -CONT $pid; fi
    sleep 20
  done
  wait $pid
}
guarded data/yang_mills_scale_corr_su2_2026_10_31.json su2 16 2.3,2.4,2.5,2.6 3600
guarded data/yang_mills_scale_corr_u1_2026_10_31.json u1 16 0.9,1.1 900
