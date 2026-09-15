#!/usr/bin/env python3
"""Boundary checks for the four-track metadata and import policy."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from benchmark_contract import PROFILE_PARAMETERS, parse_unsafe_index, parse_radius, split_track, parse_centibits
ROOT=Path(__file__).resolve().parents[1]
class ContractTests(unittest.TestCase):
    def test_profile_manifest(self):
        manifest=json.loads((ROOT/'challenges.json').read_text())
        self.assertEqual(len(manifest['challenges']),4)
        for rate,p in PROFILE_PARAMETERS.items():
            for key,value in p.items(): self.assertEqual(manifest['profiles'][rate][key],value)
    def test_score_contract(self):
        self.assertEqual(parse_centibits('10624'),10624)
        for value in ['-1','01','1.1','100001']:
            with self.assertRaises(ValueError): parse_centibits(value)
        manifest=json.loads((ROOT/'benchmark.json').read_text())
        for track in manifest['tracks']:
            self.assertEqual(track['direction'],'+' if track['name'].endswith('lower') else '-')
        for rate in PROFILE_PARAMETERS:
            for side in ['lower','upper']:
                config=json.loads((ROOT/f'benchmark/comparator-{rate}-{side}.json').read_text())
                self.assertEqual(config['solution_module'],f'ProximityPrize.Submission{rate.title()}{side.title()}.Solution')
    def test_upper_boundaries(self):
        for rate,p in PROFILE_PARAMETERS.items():
            last=p['domainSize']-p['baseDimension']
            self.assertEqual(parse_unsafe_index(str(last),profile=rate),last)
            for s in ['0',str(last+1),'01','1.0','-1']:
                with self.assertRaises(ValueError): parse_unsafe_index(s,profile=rate)
    def test_cross_profile_index(self):
        self.assertEqual(parse_unsafe_index(str(2**21),profile='half'),2**21)
        with self.assertRaises(ValueError): parse_unsafe_index(str(2**21),profile='quarter')
    def test_tracks(self):
        for rate in PROFILE_PARAMETERS:
            for side in ['lower','upper']: self.assertEqual(split_track(rate+'-'+side),(rate,side))
        with self.assertRaises(ValueError): split_track('upper')
        with self.assertRaises(ValueError): parse_radius('1/0')
    def test_renderer(self):
        with tempfile.TemporaryDirectory() as tmp:
            for rate in PROFILE_PARAMETERS:
                for side in ['lower','upper']:
                    target=Path(tmp)/'target.lean'
                    claim='1/4' if side=='lower' else '100'
                    subprocess.run(['python3',str(ROOT/'scripts/render-benchmark-challenge.py'),rate+'-'+side,'1',claim,str(target)],check=True)
                    text=target.read_text()
                    prefix='Quarter' if rate=='quarter' else ''
                    self.assertIn('import ProximityPrize.Benchmark.'+prefix+'Target'+side.title(),text)
                    namespace='ProximityPrize.Benchmark'+('.Quarter' if rate=='quarter' else '')+('.Upper' if side=='upper' else '')
                    self.assertIn('namespace '+namespace+'\n',text)
    def test_cross_track_import_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            (d/'score.txt').write_text('11681\n');(d/'unsafe-index.txt').write_text('1966080\n')
            (d/'Solution.lean').write_text('import ProximityPrize.Benchmark.QuarterTargetUpper\n')
            result=subprocess.run(['bash',str(ROOT/'scripts/check-submission-imports.sh'),'half-upper',str(d)],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            (d/'Solution.lean').write_text('import ProximityPrize.Benchmark.TargetUpper\n')
            result=subprocess.run(['bash',str(ROOT/'scripts/check-submission-imports.sh'),'half-upper',str(d)],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
if __name__=='__main__': unittest.main()
