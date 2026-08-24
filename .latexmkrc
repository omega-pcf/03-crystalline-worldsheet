$pdf_mode = 1;
$postscript_mode = $dvi_mode = 0;
$pdflatex = 'pdflatex -interaction=nonstopmode -recorder %O %S';
$bibtex_use = 2;
$out_dir = 'build';

# biber support for biblatex
@generated_exts = qw(aux bbl bcf blg fdb_latexmk fls run.xml);
add_cus_dep('bcf', 'bbl', 0, 'runbiber');
sub runbiber {
  my @deps = grep { /(\.bcf)$/ } @_;
  return system "biber @_";
}
